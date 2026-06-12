#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/ioctl.h>

#include <sys/stat.h>
#include <sys/sysmacros.h> /* For makedev() */

#include <fcntl.h>
#include <linux/fb.h>
#include <linux/input.h>

#include <assert.h>
#include <errno.h>
#include <pthread.h>

/* libvncserver */
#include "rfb/rfb.h"

#include "touch.h"
#include "logging.h"

static int touchfd = -1;

static int xmin, xmax;
static int ymin, ymax;
static int rotate;
static int trkg_id = -1;

#define TOUCH_EVENT_QUEUE_CAPACITY 4096
#define TOUCH_MIN_PRESS_US 12000

typedef struct touch_queue_item_t
{
    enum MouseAction mouseAction;
    int x;
    int y;
    int xres;
    int yres;
    uint64_t enqueue_ts_us;
} touch_queue_item_t;

static touch_queue_item_t touch_event_queue[TOUCH_EVENT_QUEUE_CAPACITY];
static unsigned int touch_queue_head = 0;
static unsigned int touch_queue_tail = 0;
static unsigned int touch_queue_count = 0;
static unsigned int touch_queue_drop_count = 0;
static unsigned int touch_queue_high_watermark = 0;
static pthread_mutex_t touch_queue_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t touch_queue_cond = PTHREAD_COND_INITIALIZER;
static pthread_t touch_worker_thread;
static int touch_worker_running = 0;
static int touch_worker_shutdown = 0;

static uint64_t touch_stats_cb_total = 0;
static uint64_t touch_stats_press = 0;
static uint64_t touch_stats_drag = 0;
static uint64_t touch_stats_release = 0;
static uint64_t touch_stats_enqueued = 0;
static uint64_t touch_stats_dequeued = 0;
static uint64_t touch_stats_dropped = 0;
static uint64_t touch_stats_write_fail = 0;
static uint64_t touch_stats_queue_delay_sum_us = 0;
static uint64_t touch_stats_queue_delay_max_us = 0;
static uint64_t touch_stats_cb_tap_gap_sum_us = 0;
static uint64_t touch_stats_cb_tap_gap_max_us = 0;
static uint64_t touch_stats_cb_tap_gap_count = 0;
static uint64_t touch_stats_inj_tap_gap_sum_us = 0;
static uint64_t touch_stats_inj_tap_gap_max_us = 0;
static uint64_t touch_stats_inj_tap_gap_count = 0;
static uint64_t touch_stats_short_press_stretched = 0;
static uint64_t touch_stats_stretch_total_us = 0;
static uint64_t touch_stats_last_log_us = 0;
static uint64_t touch_last_press_cb_us = 0;
static uint64_t touch_last_press_inj_us = 0;

#ifndef input_event_sec
#define input_event_sec time.tv_sec
#define input_event_usec time.tv_usec
#endif

static uint64_t touch_now_us(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000000ULL + (uint64_t)tv.tv_usec;
}

static void touch_maybe_log_stats(int force)
{
    uint64_t now_us = touch_now_us();
    if (!force)
    {
        if (touch_stats_last_log_us != 0 && (now_us - touch_stats_last_log_us) < 2000000ULL)
            return;
    }

    touch_stats_last_log_us = now_us;

    uint64_t avg_delay_us = 0;
    if (touch_stats_dequeued > 0)
        avg_delay_us = touch_stats_queue_delay_sum_us / touch_stats_dequeued;

    uint64_t avg_cb_tap_gap_us = 0;
    if (touch_stats_cb_tap_gap_count > 0)
        avg_cb_tap_gap_us = touch_stats_cb_tap_gap_sum_us / touch_stats_cb_tap_gap_count;

    uint64_t avg_inj_tap_gap_us = 0;
    if (touch_stats_inj_tap_gap_count > 0)
        avg_inj_tap_gap_us = touch_stats_inj_tap_gap_sum_us / touch_stats_inj_tap_gap_count;

    uint64_t avg_stretch_us = 0;
    if (touch_stats_short_press_stretched > 0)
        avg_stretch_us = touch_stats_stretch_total_us / touch_stats_short_press_stretched;

    info_print("touch-debug: cb=%llu press=%llu drag=%llu release=%llu enq=%llu deq=%llu drop=%llu q=%u hi=%u qdelay(us){avg=%llu max=%llu} tapgap_cb(us){avg=%llu max=%llu n=%llu} tapgap_inj(us){avg=%llu max=%llu n=%llu} stretch(us){n=%llu avg=%llu} write_fail=%llu\n",
               (unsigned long long)touch_stats_cb_total,
               (unsigned long long)touch_stats_press,
               (unsigned long long)touch_stats_drag,
               (unsigned long long)touch_stats_release,
               (unsigned long long)touch_stats_enqueued,
               (unsigned long long)touch_stats_dequeued,
               (unsigned long long)touch_stats_dropped,
               touch_queue_count,
               touch_queue_high_watermark,
               (unsigned long long)avg_delay_us,
               (unsigned long long)touch_stats_queue_delay_max_us,
               (unsigned long long)avg_cb_tap_gap_us,
               (unsigned long long)touch_stats_cb_tap_gap_max_us,
               (unsigned long long)touch_stats_cb_tap_gap_count,
               (unsigned long long)avg_inj_tap_gap_us,
               (unsigned long long)touch_stats_inj_tap_gap_max_us,
               (unsigned long long)touch_stats_inj_tap_gap_count,
               (unsigned long long)touch_stats_short_press_stretched,
               (unsigned long long)avg_stretch_us,
               (unsigned long long)touch_stats_write_fail);
}

static void write_event_or_count_fail(struct input_event *ev)
{
    if (write(touchfd, ev, sizeof(*ev)) < 0)
    {
        error_print("write event failed, %s\n", strerror(errno));
        touch_stats_write_fail++;
    }
}

static void inject_touch_event_immediate(enum MouseAction mouseAction,
                                         int x,
                                         int y,
                                         int xres,
                                         int yres)
{
    uint64_t inject_now_us = touch_now_us();
    struct input_event ev;
    int xin = x;
    int yin = y;

    switch (rotate)
    {
    case 90:
        x = yin;
        y = yres - 1 - xin;
        break;
    case 180:
        x = xres - 1 - xin;
        y = yres - 1 - yin;
        break;
    case 270:
        x = xres - 1 - yin;
        y = xin;
        break;
    }

    x = xmin + (x * (xmax - xmin)) / xres;
    y = ymin + (y * (ymax - ymin)) / yres;

    memset(&ev, 0, sizeof(ev));

    bool sendPos;
    bool sendTouch;
    int trkIdValue;
    int touchValue;
    struct timeval time;

    switch (mouseAction)
    {
    case MousePress:
        sendPos = true;
        sendTouch = true;
        trkIdValue = ++trkg_id;
        touchValue = 1;
        touch_last_press_inj_us = inject_now_us;
        break;
    case MouseRelease:
        sendPos = false;
        sendTouch = true;
        trkIdValue = -1;
        touchValue = 0;
        if (touch_last_press_inj_us != 0)
        {
            uint64_t gap_us = inject_now_us - touch_last_press_inj_us;
            touch_stats_inj_tap_gap_sum_us += gap_us;
            touch_stats_inj_tap_gap_count++;
            if (gap_us > touch_stats_inj_tap_gap_max_us)
                touch_stats_inj_tap_gap_max_us = gap_us;

            if (gap_us < TOUCH_MIN_PRESS_US)
            {
                uint64_t stretch_us = TOUCH_MIN_PRESS_US - gap_us;
                touch_stats_short_press_stretched++;
                touch_stats_stretch_total_us += stretch_us;
                usleep((useconds_t)stretch_us);
                inject_now_us = touch_now_us();
            }
        }
        break;
    case MouseDrag:
        sendPos = true;
        sendTouch = false;
        break;
    default:
        error_print("invalid mouse action\n");
        return;
    }

    if (sendTouch)
    {
        gettimeofday(&time, 0);
        ev.input_event_sec = time.tv_sec;

        ev.type = EV_ABS;
        ev.code = ABS_MT_TRACKING_ID;
        ev.value = trkIdValue;
        write_event_or_count_fail(&ev);

        gettimeofday(&time, 0);
        ev.input_event_sec = time.tv_sec;
        ev.input_event_usec = time.tv_usec;
        ev.type = EV_KEY;
        ev.code = BTN_TOUCH;
        ev.value = touchValue;
        write_event_or_count_fail(&ev);
    }

    if (sendPos)
    {
        gettimeofday(&time, 0);
        ev.input_event_sec = time.tv_sec;
        ev.input_event_usec = time.tv_usec;
        ev.type = EV_ABS;
        ev.code = ABS_MT_POSITION_X;
        ev.value = x;
        write_event_or_count_fail(&ev);

        gettimeofday(&time, 0);
        ev.input_event_sec = time.tv_sec;
        ev.input_event_usec = time.tv_usec;
        ev.type = EV_ABS;
        ev.code = ABS_MT_POSITION_Y;
        ev.value = y;
        write_event_or_count_fail(&ev);

        gettimeofday(&time, 0);
        ev.input_event_sec = time.tv_sec;
        ev.input_event_usec = time.tv_usec;
        ev.type = EV_ABS;
        ev.code = ABS_X;
        ev.value = x;
        write_event_or_count_fail(&ev);

        gettimeofday(&time, 0);
        ev.input_event_sec = time.tv_sec;
        ev.input_event_usec = time.tv_usec;
        ev.type = EV_ABS;
        ev.code = ABS_Y;
        ev.value = y;
        write_event_or_count_fail(&ev);
    }

    gettimeofday(&time, 0);
    ev.input_event_sec = time.tv_sec;
    ev.input_event_usec = time.tv_usec;
    ev.type = EV_SYN;
    ev.code = 0;
    ev.value = 0;
    write_event_or_count_fail(&ev);

    info_print("injectTouchEvent (screen(%d,%d) -> touch(%d,%d), mouse=%d)\n", xin, yin, x, y, mouseAction);
}

static void *touch_worker_main(void *opaque)
{
    (void)opaque;

    for (;;)
    {
        touch_queue_item_t item;

        pthread_mutex_lock(&touch_queue_mutex);
        while (touch_queue_count == 0 && !touch_worker_shutdown)
            pthread_cond_wait(&touch_queue_cond, &touch_queue_mutex);

        if (touch_queue_count == 0 && touch_worker_shutdown)
        {
            pthread_mutex_unlock(&touch_queue_mutex);
            break;
        }

        item = touch_event_queue[touch_queue_head];
        touch_queue_head = (touch_queue_head + 1u) % TOUCH_EVENT_QUEUE_CAPACITY;
        touch_queue_count--;
        touch_stats_dequeued++;
        pthread_mutex_unlock(&touch_queue_mutex);

        {
            uint64_t now_us = touch_now_us();
            uint64_t delay_us = now_us - item.enqueue_ts_us;
            touch_stats_queue_delay_sum_us += delay_us;
            if (delay_us > touch_stats_queue_delay_max_us)
                touch_stats_queue_delay_max_us = delay_us;
        }

        inject_touch_event_immediate(item.mouseAction, item.x, item.y, item.xres, item.yres);
        touch_maybe_log_stats(0);
    }

    return NULL;
}

int init_touch(const char *touch_device, int vnc_rotate)
{
    info_print("Initializing touch device %s ...\n", touch_device);
    struct input_absinfo info;
    if ((touchfd = open(touch_device, O_RDWR)) == -1)
    {
        error_print("cannot open touch device %s\n", touch_device);
        return 0;
    }

    if (ioctl(touchfd, EVIOCGABS(ABS_X), &info))
    {
        error_print("cannot get ABS_X info, %s\n", strerror(errno));
        return 0;
    }
    xmin = info.minimum;
    xmax = info.maximum;

    if (ioctl(touchfd, EVIOCGABS(ABS_Y), &info))
    {
        error_print("cannot get ABS_Y, %s\n", strerror(errno));
        return 0;
    }
    ymin = info.minimum;
    ymax = info.maximum;
    rotate = vnc_rotate;

    touch_queue_head = 0;
    touch_queue_tail = 0;
    touch_queue_count = 0;
    touch_queue_drop_count = 0;
    touch_queue_high_watermark = 0;
    touch_worker_shutdown = 0;

    touch_stats_cb_total = 0;
    touch_stats_press = 0;
    touch_stats_drag = 0;
    touch_stats_release = 0;
    touch_stats_enqueued = 0;
    touch_stats_dequeued = 0;
    touch_stats_dropped = 0;
    touch_stats_write_fail = 0;
    touch_stats_queue_delay_sum_us = 0;
    touch_stats_queue_delay_max_us = 0;
    touch_stats_cb_tap_gap_sum_us = 0;
    touch_stats_cb_tap_gap_max_us = 0;
    touch_stats_cb_tap_gap_count = 0;
    touch_stats_inj_tap_gap_sum_us = 0;
    touch_stats_inj_tap_gap_max_us = 0;
    touch_stats_inj_tap_gap_count = 0;
    touch_stats_short_press_stretched = 0;
    touch_stats_stretch_total_us = 0;
    touch_stats_last_log_us = 0;
    touch_last_press_cb_us = 0;
    touch_last_press_inj_us = 0;

    if (pthread_create(&touch_worker_thread, NULL, touch_worker_main, NULL) != 0)
    {
        error_print("cannot start touch worker thread, %s\n", strerror(errno));
        close(touchfd);
        touchfd = -1;
        return 0;
    }
    touch_worker_running = 1;

    info_print("  x:(%d %d)  y:(%d %d) \n", xmin, xmax, ymin, ymax);
    return 1;
}

void cleanup_touch()
{
    if (touch_worker_running)
    {
        pthread_mutex_lock(&touch_queue_mutex);
        touch_worker_shutdown = 1;
        pthread_cond_signal(&touch_queue_cond);
        pthread_mutex_unlock(&touch_queue_mutex);

        pthread_join(touch_worker_thread, NULL);
        touch_worker_running = 0;
    }

    touch_maybe_log_stats(1);

    if (touchfd != -1)
    {
        close(touchfd);
        touchfd = -1;
    }
}

void injectTouchEvent(enum MouseAction mouseAction, int x, int y, struct fb_var_screeninfo *scrinfo)
{
    uint64_t cb_now_us = touch_now_us();

    touch_stats_cb_total++;
    if (mouseAction == MousePress)
    {
        touch_stats_press++;
        touch_last_press_cb_us = cb_now_us;
    }
    else if (mouseAction == MouseDrag)
    {
        touch_stats_drag++;
    }
    else if (mouseAction == MouseRelease)
    {
        touch_stats_release++;
        if (touch_last_press_cb_us != 0)
        {
            uint64_t gap_us = cb_now_us - touch_last_press_cb_us;
            touch_stats_cb_tap_gap_sum_us += gap_us;
            touch_stats_cb_tap_gap_count++;
            if (gap_us > touch_stats_cb_tap_gap_max_us)
                touch_stats_cb_tap_gap_max_us = gap_us;
        }
    }

    if (!touch_worker_running)
    {
        inject_touch_event_immediate(mouseAction, x, y, scrinfo->xres, scrinfo->yres);
        touch_maybe_log_stats(0);
        return;
    }

    pthread_mutex_lock(&touch_queue_mutex);

    if (touch_queue_count >= TOUCH_EVENT_QUEUE_CAPACITY)
    {
        touch_queue_head = (touch_queue_head + 1u) % TOUCH_EVENT_QUEUE_CAPACITY;
        touch_queue_count--;
        touch_queue_drop_count++;
        touch_stats_dropped++;
        if ((touch_queue_drop_count % 100u) == 0u)
            info_print("touch queue dropped %u events\n", touch_queue_drop_count);
    }

    touch_queue_item_t *item = &touch_event_queue[touch_queue_tail];
    item->mouseAction = mouseAction;
    item->x = x;
    item->y = y;
    item->xres = scrinfo->xres;
    item->yres = scrinfo->yres;
    item->enqueue_ts_us = cb_now_us;

    touch_queue_tail = (touch_queue_tail + 1u) % TOUCH_EVENT_QUEUE_CAPACITY;
    touch_queue_count++;
    touch_stats_enqueued++;
    if (touch_queue_count > touch_queue_high_watermark)
        touch_queue_high_watermark = touch_queue_count;

    pthread_cond_signal(&touch_queue_cond);
    pthread_mutex_unlock(&touch_queue_mutex);

    touch_maybe_log_stats(0);
}
