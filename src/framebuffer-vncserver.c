/*
 * $Id$
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * This project is an adaptation of the original fbvncserver for the iPAQ
 * and Zaurus.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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
#include "rfb/keysym.h"

#include "touch.h"
#include "mouse.h"
#include "keyboard.h"
#include "logging.h"

/*****************************************************************************/
#define LOG_FPS

#define OUTPUT_BITS_PER_SAMPLE 5
#define OUTPUT_SAMPLES_PER_PIXEL 3
#define OUTPUT_BYTES_PER_PIXEL 2
#define DIRTY_TILE_SIZE 16
#define TILE_CACHE_FRAME_MULTIPLIER 5
#define TILE_CACHE_MIN_ENTRIES 256
#define TILE_BUILD_QUEUE_MULTIPLIER 2
#define DEBUG_TILE_MODE 0

// #define CHANNELS_PER_PIXEL 4

static char fb_device[256] = "/dev/fb0";
static char touch_device[256] = "";
static char kbd_device[256] = "";
static char mouse_device[256] = "";

static struct fb_var_screeninfo var_scrinfo;
static struct fb_fix_screeninfo fix_scrinfo;
static int fbfd = -1;
static unsigned short int *fbmmap = MAP_FAILED;
static uint8_t *vncbuf;
static uint8_t *vnc_prevbuf;

static int vnc_port = 5900;
static int vnc_rotate = 0;
static int touch_rotate = -1;
static int target_fps = 10;
static rfbScreenInfoPtr server;
static size_t bytespp;
static unsigned int bits_per_pixel;
static unsigned int frame_size;
static unsigned int fb_xres;
static unsigned int fb_yres;
static unsigned int relay_xres;
static unsigned int relay_yres;
static unsigned int relay_frame_size;
static unsigned int relay_tile_cols;
static unsigned int relay_tile_rows;
static unsigned int relay_tile_count;
static uint8_t *tile_dirty;
static uint8_t *tile_render_from_cache;
static uint8_t *tile_debug_corner_state;
static struct tile_hash_t *tile_last_served_hash;
static uint8_t *tile_last_served_valid;
static struct tile_hash_t *tile_frame_hash;
static struct tile_hash_t *tile_prev_frame_hash;
static uint8_t *tile_prev_frame_hash_valid;
static int *tile_copy_source_index;
static int *copy_anchor_map_slot;
static unsigned int copy_anchor_map_capacity = 0;
static int *tile_cache_map_index;
static uint8_t *tile_cache_map_state;
static unsigned int tile_cache_map_capacity = 0;
static int *tile_cache_index;
static uint16_t *relay_nn_snapshot;
static uint8_t *fb_shadow_front;
static uint8_t *fb_shadow_back;
static pthread_t fb_shadow_copy_thread;
static int fb_shadow_copy_inflight = 0;
static int fb_shadow_initialized = 0;
static unsigned int downsample_factor = 4;
static unsigned int detect_sample_step = 2;
static unsigned int detect_verify_interval = 0;
static int use_sequential_dump = 0;
static int use_shadow_copy = 0;
static int force_full_tile_refresh = 1;
static int vsync_wait_enabled = 1;
static uint64_t cache_use_tick = 0;

typedef struct fb_shadow_copy_job_t
{
    const uint8_t *src;
    uint8_t *dst;
    size_t bytes;
} fb_shadow_copy_job_t;

static fb_shadow_copy_job_t fb_shadow_copy_job;

#define CACHE_MAP_EMPTY 0
#define CACHE_MAP_OCCUPIED 1
#define CACHE_MAP_TOMBSTONE 2

typedef struct tile_hash_t
{
    uint64_t h1;
    uint64_t h2;
} tile_hash_t;

typedef struct tile_cache_entry_t
{
    tile_hash_t hash;
    uint64_t last_used_tick;
    uint16_t width;
    uint16_t height;
    uint8_t valid;
    uint8_t pixels[DIRTY_TILE_SIZE * DIRTY_TILE_SIZE * OUTPUT_BYTES_PER_PIXEL];
} tile_cache_entry_t;

typedef struct tile_build_task_t
{
    uint16_t width;
    uint16_t height;
    uint16_t tile_x0;
    uint16_t tile_y0;
    uint16_t base_w;
    uint16_t base_h;
} tile_build_task_t;

static tile_cache_entry_t *tile_cache;
static tile_build_task_t *tile_build_queue;
static unsigned int tile_cache_capacity = 0;
static unsigned int tile_build_queue_capacity = 0;
static unsigned int tile_build_queue_head = 0;
static unsigned int tile_build_queue_tail = 0;
static unsigned int tile_build_queue_count = 0;
int verbose = 0;
static volatile uint64_t fb_probe_sink = 0;

#define UNUSED(x) (void)(x)

/* No idea, just copied from fbvncserver as part of the frame differerencing
 * algorithm.  I will probably be later rewriting all of this. */
static struct varblock_t
{
    int min_i;
    int min_j;
    int max_i;
    int max_j;
    int r_offset;
    int g_offset;
    int b_offset;
    int rfb_xres;
    int rfb_maxy;
} varblock;

/*****************************************************************************/

static void init_fb(void)
{
    size_t pixels;

    if ((fbfd = open(fb_device, O_RDONLY)) == -1)
    {
        error_print("cannot open fb device %s\n", fb_device);
        exit(EXIT_FAILURE);
    }

    if (ioctl(fbfd, FBIOGET_VSCREENINFO, &var_scrinfo) != 0)
    {
        error_print("ioctl error\n");
        exit(EXIT_FAILURE);
    }

    if (ioctl(fbfd, FBIOGET_FSCREENINFO, &fix_scrinfo) != 0)
    {
        error_print("ioctl error\n");
        exit(EXIT_FAILURE);
    }

    /*
     * Get actual resolution of the framebufffer, which is not always the same as the screen resolution.
     * This prevents the screen from 'smearing' on 1366 x 768 displays
     */

    fb_xres = fix_scrinfo.line_length / (var_scrinfo.bits_per_pixel / 8.0);
    fb_yres = var_scrinfo.yres;

    pixels = fb_xres * fb_yres;
    bytespp = var_scrinfo.bits_per_pixel / 8;
    bits_per_pixel = var_scrinfo.bits_per_pixel;
    frame_size = pixels * bits_per_pixel / 8;

    info_print("  xres=%d, yres=%d, xresv=%d, yresv=%d, xoffs=%d, yoffs=%d, bpp=%d\n",
               (int)fb_xres, (int)fb_yres,
               (int)var_scrinfo.xres_virtual, (int)var_scrinfo.yres_virtual,
               (int)var_scrinfo.xoffset, (int)var_scrinfo.yoffset,
               (int)var_scrinfo.bits_per_pixel);
    info_print("  offset:length red=%d:%d green=%d:%d blue=%d:%d \n",
               (int)var_scrinfo.red.offset, (int)var_scrinfo.red.length,
               (int)var_scrinfo.green.offset, (int)var_scrinfo.green.length,
               (int)var_scrinfo.blue.offset, (int)var_scrinfo.blue.length);

    fbmmap = mmap(NULL, frame_size, PROT_READ, MAP_SHARED, fbfd, 0);

    if (fbmmap == MAP_FAILED)
    {
        error_print("mmap failed\n");
        exit(EXIT_FAILURE);
    }
}

static void cleanup_fb(void)
{
    if (fbfd != -1)
    {
        close(fbfd);
        fbfd = -1;
    }
}

static void keyevent(rfbBool down, rfbKeySym key, rfbClientPtr cl)
{
    int scancode;

    debug_print("Got keysym: %04x (down=%d)\n", (unsigned int)key, (int)down);

    if ((scancode = keysym2scancode(key, cl)))
    {
        injectKeyEvent(scancode, down);
    }
}

static void ptrevent_touch(int buttonMask, int x, int y, rfbClientPtr cl)
{
    UNUSED(cl);
    /* Indicates either pointer movement or a pointer button press or release. The pointer is
now at (x-position, y-position), and the current state of buttons 1 to 8 are represented
by bits 0 to 7 of button-mask respectively, 0 meaning up, 1 meaning down (pressed).
On a conventional mouse, buttons 1, 2 and 3 correspond to the left, middle and right
buttons on the mouse. On a wheel mouse, each step of the wheel upwards is represented
by a press and release of button 4, and each step downwards is represented by
a press and release of button 5.
  From: http://www.vislab.usyd.edu.au/blogs/index.php/2009/05/22/an-headerless-indexed-protocol-for-input-1?blog=61 */

    debug_print("Got ptrevent: %04x (x=%d, y=%d)\n", buttonMask, x, y);

    /* VNC output is downsampled; map pointer coordinates back to source. */
    int scaled_x = x * (int)downsample_factor;
    int scaled_y = y * (int)downsample_factor;
    if (scaled_x >= (int)var_scrinfo.xres)
        scaled_x = (int)var_scrinfo.xres - 1;
    if (scaled_y >= (int)var_scrinfo.yres)
        scaled_y = (int)var_scrinfo.yres - 1;
    // Simulate left mouse event as touch event.
    // Drive state from bit-0 transitions so release is not missed when other bits are set.
    static int pressed = 0;
    int primary_down = (buttonMask & 1) != 0;

    if (primary_down)
    {
        if (pressed)
            injectTouchEvent(MouseDrag, scaled_x, scaled_y, &var_scrinfo);
        else
        {
            pressed = 1;
            injectTouchEvent(MousePress, scaled_x, scaled_y, &var_scrinfo);
        }
    }
    else if (pressed)
    {
        pressed = 0;
        injectTouchEvent(MouseRelease, scaled_x, scaled_y, &var_scrinfo);
    }
}

static void ptrevent_mouse(int buttonMask, int x, int y, rfbClientPtr cl)
{
    UNUSED(cl);
    /* Indicates either pointer movement or a pointer button press or release. The pointer is
now at (x-position, y-position), and the current state of buttons 1 to 8 are represented
by bits 0 to 7 of button-mask respectively, 0 meaning up, 1 meaning down (pressed).
On a conventional mouse, buttons 1, 2 and 3 correspond to the left, middle and right
buttons on the mouse. On a wheel mouse, each step of the wheel upwards is represented
by a press and release of button 4, and each step downwards is represented by
a press and release of button 5.
  From: http://www.vislab.usyd.edu.au/blogs/index.php/2009/05/22/an-headerless-indexed-protocol-for-input-1?blog=61 */

    debug_print("Got mouse: %04x (x=%d, y=%d)\n", buttonMask, x, y);

    /* VNC output is downsampled; map pointer coordinates back to source. */
    int scaled_x = x * (int)downsample_factor;
    int scaled_y = y * (int)downsample_factor;
    if (scaled_x >= (int)var_scrinfo.xres)
        scaled_x = (int)var_scrinfo.xres - 1;
    if (scaled_y >= (int)var_scrinfo.yres)
        scaled_y = (int)var_scrinfo.yres - 1;

    // Simulate left mouse event as touch event
    injectMouseEvent(&var_scrinfo, buttonMask, scaled_x, scaled_y);
}

/*****************************************************************************/

static void init_fb_server(int argc, char **argv, rfbBool enable_touch, rfbBool enable_mouse)
{
    info_print("Initializing server...\n");

    int rbytespp = OUTPUT_BYTES_PER_PIXEL;
    relay_xres = fb_xres / downsample_factor;
    relay_yres = fb_yres / downsample_factor;
    if (relay_xres == 0)
        relay_xres = 1;
    if (relay_yres == 0)
        relay_yres = 1;

    if (vnc_rotate == 90 || vnc_rotate == 270)
    {
        unsigned int tmp = relay_xres;
        relay_xres = relay_yres;
        relay_yres = tmp;
    }

    relay_frame_size = relay_xres * relay_yres * rbytespp;

    /* Allocate the VNC server buffer to be managed (not manipulated) by
     * libvncserver. */
    vncbuf = malloc(relay_frame_size);
    assert(vncbuf != NULL);
    memset(vncbuf, 0x00, relay_frame_size);

    /* Keep previous sent frame for dirty-rectangle detection. */
    vnc_prevbuf = malloc(relay_frame_size);
    assert(vnc_prevbuf != NULL);
    memcpy(vnc_prevbuf, vncbuf, relay_frame_size);

    relay_tile_cols = (relay_xres + DIRTY_TILE_SIZE - 1) / DIRTY_TILE_SIZE;
    relay_tile_rows = (relay_yres + DIRTY_TILE_SIZE - 1) / DIRTY_TILE_SIZE;
    relay_tile_count = relay_tile_cols * relay_tile_rows;

    tile_dirty = malloc(relay_tile_count);
    tile_render_from_cache = malloc(relay_tile_count);
    tile_debug_corner_state = malloc(relay_tile_count);
    tile_last_served_hash = calloc(relay_tile_count, sizeof(tile_hash_t));
    tile_last_served_valid = calloc(relay_tile_count, sizeof(uint8_t));
    tile_frame_hash = calloc(relay_tile_count, sizeof(tile_hash_t));
    tile_prev_frame_hash = calloc(relay_tile_count, sizeof(tile_hash_t));
    tile_prev_frame_hash_valid = calloc(relay_tile_count, sizeof(uint8_t));
    tile_copy_source_index = malloc(relay_tile_count * sizeof(int));
    tile_cache_index = malloc(relay_tile_count * sizeof(int));

    copy_anchor_map_capacity = 1;
    while (copy_anchor_map_capacity < (relay_tile_count * 2))
        copy_anchor_map_capacity <<= 1;
    copy_anchor_map_slot = malloc(copy_anchor_map_capacity * sizeof(int));

    assert(tile_dirty != NULL);
    assert(tile_render_from_cache != NULL);
    assert(tile_debug_corner_state != NULL);
    assert(tile_last_served_hash != NULL);
    assert(tile_last_served_valid != NULL);
    assert(tile_frame_hash != NULL);
    assert(tile_prev_frame_hash != NULL);
    assert(tile_prev_frame_hash_valid != NULL);
    assert(tile_copy_source_index != NULL);
    assert(copy_anchor_map_slot != NULL);
    assert(tile_cache_index != NULL);
    memset(tile_dirty, 0, relay_tile_count);
    memset(tile_render_from_cache, 0, relay_tile_count);
    memset(tile_debug_corner_state, 0, relay_tile_count);
    memset(tile_last_served_valid, 0, relay_tile_count);
    memset(tile_prev_frame_hash_valid, 0, relay_tile_count);
    memset(tile_copy_source_index, 0xFF, relay_tile_count * sizeof(int));
    memset(copy_anchor_map_slot, 0xFF, copy_anchor_map_capacity * sizeof(int));
    for (unsigned int i = 0; i < relay_tile_count; i++)
        tile_cache_index[i] = -1;

    tile_cache_capacity = relay_tile_count * TILE_CACHE_FRAME_MULTIPLIER;
    if (tile_cache_capacity < TILE_CACHE_MIN_ENTRIES)
        tile_cache_capacity = TILE_CACHE_MIN_ENTRIES;

    tile_build_queue_capacity = relay_tile_count * TILE_BUILD_QUEUE_MULTIPLIER;
    if (tile_build_queue_capacity < relay_tile_count)
        tile_build_queue_capacity = relay_tile_count;

    tile_cache_map_capacity = 1;
    while (tile_cache_map_capacity < (tile_cache_capacity * 2))
        tile_cache_map_capacity <<= 1;

    tile_cache = calloc(tile_cache_capacity, sizeof(tile_cache_entry_t));
    tile_build_queue = calloc(tile_build_queue_capacity, sizeof(tile_build_task_t));
    tile_cache_map_index = malloc(tile_cache_map_capacity * sizeof(int));
    tile_cache_map_state = calloc(tile_cache_map_capacity, sizeof(uint8_t));
    relay_nn_snapshot = malloc(relay_xres * relay_yres * sizeof(uint16_t));
    fb_shadow_front = malloc(frame_size);
    fb_shadow_back = malloc(frame_size);
    assert(tile_cache != NULL);
    assert(tile_build_queue != NULL);
    assert(tile_cache_map_index != NULL);
    assert(tile_cache_map_state != NULL);
    assert(relay_nn_snapshot != NULL);
    assert(fb_shadow_front != NULL);
    assert(fb_shadow_back != NULL);
    memset(tile_cache_map_index, 0xFF, tile_cache_map_capacity * sizeof(int));

    info_print("\ttile cache entries: %u (~%u frames)\n",
               tile_cache_capacity,
               relay_tile_count == 0 ? 0 : (tile_cache_capacity / relay_tile_count));

    tile_build_queue_head = 0;
    tile_build_queue_tail = 0;
    tile_build_queue_count = 0;
    cache_use_tick = 0;

    /* TODO: This assumes var_scrinfo.bits_per_pixel is 16. */
    server = rfbGetScreen(&argc, argv, relay_xres, relay_yres,
                          OUTPUT_BITS_PER_SAMPLE, OUTPUT_SAMPLES_PER_PIXEL, rbytespp);
    assert(server != NULL);

    server->serverFormat.bitsPerPixel = 16;
    server->serverFormat.depth = 16;
    server->serverFormat.trueColour = TRUE;
    server->serverFormat.redMax = 31;
    server->serverFormat.greenMax = 63;
    server->serverFormat.blueMax = 31;
    server->serverFormat.redShift = 11;
    server->serverFormat.greenShift = 5;
    server->serverFormat.blueShift = 0;

    server->desktopName = "framebuffer";
    server->frameBuffer = (char *)vncbuf;
    server->alwaysShared = TRUE;
    server->httpDir = NULL;
    server->port = vnc_port;

    server->kbdAddEvent = keyevent;
    if (enable_touch)
    {
        server->ptrAddEvent = ptrevent_touch;
    }

    if (enable_mouse)
    {
        server->ptrAddEvent = ptrevent_mouse;
    }
    

    rfbInitServer(server);

    /* Mark as dirty since we haven't sent any updates at all yet. */
    rfbMarkRectAsModified(server, 0, 0, relay_xres, relay_yres);

    /* No idea. */
    varblock.r_offset = var_scrinfo.red.offset + var_scrinfo.red.length - OUTPUT_BITS_PER_SAMPLE;
    varblock.g_offset = var_scrinfo.green.offset + var_scrinfo.green.length - OUTPUT_BITS_PER_SAMPLE;
    varblock.b_offset = var_scrinfo.blue.offset + var_scrinfo.blue.length - OUTPUT_BITS_PER_SAMPLE;
    varblock.rfb_xres = relay_yres;
    varblock.rfb_maxy = relay_xres - 1;
}

// sec
#define LOG_TIME 5

int timeToLogFPS()
{
    static struct timeval now = {0, 0}, then = {0, 0};
    double elapsed, dnow, dthen;
    gettimeofday(&now, NULL);
    dnow = now.tv_sec + (now.tv_usec / 1000000.0);
    dthen = then.tv_sec + (then.tv_usec / 1000000.0);
    elapsed = dnow - dthen;
    if (elapsed > LOG_TIME)
        memcpy((char *)&then, (char *)&now, sizeof(struct timeval));
    return elapsed > LOG_TIME;
}

/*****************************************************************************/
//#define COLOR_MASK  0x1f001f
static uint32_t channel_mask(unsigned int length)
{
    if (length == 0)
        return 0;
    if (length >= 32)
        return 0xFFFFFFFFu;
    return (1u << length) - 1u;
}

static uint32_t extract_channel_value(uint32_t pixel, struct fb_bitfield channel)
{
    uint32_t mask = channel_mask(channel.length);
    if (mask == 0)
        return 0;
    return (pixel >> channel.offset) & mask;
}

static uint32_t scale_channel_bits(uint32_t value, unsigned int in_bits, unsigned int out_bits)
{
    if (out_bits == 0 || in_bits == 0)
        return 0;

    if (in_bits == out_bits)
        return value & channel_mask(out_bits);

    uint32_t in_max = channel_mask(in_bits);
    uint32_t out_max = channel_mask(out_bits);
    if (in_max == 0)
        return 0;

    return (uint32_t)(((uint64_t)value * out_max + (in_max / 2u)) / in_max);
}

static uint16_t packed_to_rgb565(uint32_t pixel)
{
    uint32_t r = extract_channel_value(pixel, var_scrinfo.red);
    uint32_t g = extract_channel_value(pixel, var_scrinfo.green);
    uint32_t b = extract_channel_value(pixel, var_scrinfo.blue);

    uint32_t r5 = scale_channel_bits(r, var_scrinfo.red.length, 5);
    uint32_t g6 = scale_channel_bits(g, var_scrinfo.green.length, 6);
    uint32_t b5 = scale_channel_bits(b, var_scrinfo.blue.length, 5);

    return (uint16_t)((r5 << 11) | (g6 << 5) | b5);
}

static void output_to_base(unsigned int dx, unsigned int dy,
                           unsigned int base_w, unsigned int base_h,
                           unsigned int *x, unsigned int *y)
{
    switch (vnc_rotate)
    {
    case 0:
        *x = dx;
        *y = dy;
        break;
    case 90:
        *x = dy;
        *y = base_h - 1 - dx;
        break;
    case 180:
        *x = base_w - 1 - dx;
        *y = base_h - 1 - dy;
        break;
    case 270:
        *x = base_w - 1 - dy;
        *y = dx;
        break;
    default:
        error_print("rotation is invalid\n");
        exit(EXIT_FAILURE);
    }
}

static inline uint32_t read_source_at(const uint8_t *src, uint32_t source_mask,
                                      unsigned int sx, unsigned int sy)
{
    if (bits_per_pixel == 1)
    {
        unsigned int bit_index = sy * fb_xres + sx;
        uint8_t byte = src[bit_index / 8];
        return (byte >> (7 - (bit_index % 8))) & 0x1u;
    }

    const uint8_t *pixel_ptr = src + ((sy * fb_xres + sx) * bytespp);
    uint32_t value;
    if (bytespp == 4)
    {
        value = *(const uint32_t *)pixel_ptr;
    }
    else if (bytespp == 2)
    {
        value = *(const uint16_t *)pixel_ptr;
    }
    else if (bytespp == 3)
    {
        value = (uint32_t)pixel_ptr[0] |
                ((uint32_t)pixel_ptr[1] << 8) |
                ((uint32_t)pixel_ptr[2] << 16);
    }
    else
    {
        value = pixel_ptr[0];
    }

    return value & source_mask;
}

static uint16_t output_pixel_to_rgb565(const uint8_t *src, uint32_t source_mask,
                                       unsigned int dx, unsigned int dy,
                                       unsigned int base_w, unsigned int base_h)
{
    unsigned int base_x, base_y;
    if (vnc_rotate == 0)
    {
        base_x = dx;
        base_y = dy;
    }
    else
    {
        output_to_base(dx, dy, base_w, base_h, &base_x, &base_y);
    }
    uint32_t sample = read_source_at(src, source_mask,
                                     base_x * downsample_factor,
                                     base_y * downsample_factor);
    if (bits_per_pixel == 1)
        return sample ? 0x0000 : 0xFFFF;
    return packed_to_rgb565(sample);
}

static uint16_t output_pixel_to_rgb565_averaged(const uint8_t *src, uint32_t source_mask,
                                                unsigned int dx, unsigned int dy,
                                                unsigned int base_w, unsigned int base_h)
{
    unsigned int base_x, base_y;
    output_to_base(dx, dy, base_w, base_h, &base_x, &base_y);

    unsigned int sx0 = base_x * downsample_factor;
    unsigned int sy0 = base_y * downsample_factor;
    unsigned int sx1 = sx0 + downsample_factor;
    unsigned int sy1 = sy0 + downsample_factor;
    if (sx1 > fb_xres)
        sx1 = fb_xres;
    if (sy1 > fb_yres)
        sy1 = fb_yres;

    if (sx0 >= sx1 || sy0 >= sy1)
        return output_pixel_to_rgb565(src, source_mask, dx, dy, base_w, base_h);

    uint64_t count = 0;
    uint64_t sum_r = 0;
    uint64_t sum_g = 0;
    uint64_t sum_b = 0;
    uint64_t sum_bw = 0;

    for (unsigned int sy = sy0; sy < sy1; sy++)
    {
        for (unsigned int sx = sx0; sx < sx1; sx++)
        {
            uint32_t sample = read_source_at(src, source_mask, sx, sy);
            if (bits_per_pixel == 1)
            {
                sum_bw += sample ? 1u : 0u;
            }
            else
            {
                uint32_t r = extract_channel_value(sample, var_scrinfo.red);
                uint32_t g = extract_channel_value(sample, var_scrinfo.green);
                uint32_t b = extract_channel_value(sample, var_scrinfo.blue);
                sum_r += scale_channel_bits(r, var_scrinfo.red.length, 5);
                sum_g += scale_channel_bits(g, var_scrinfo.green.length, 6);
                sum_b += scale_channel_bits(b, var_scrinfo.blue.length, 5);
            }
            count++;
        }
    }

    if (count == 0)
        return output_pixel_to_rgb565(src, source_mask, dx, dy, base_w, base_h);

    if (bits_per_pixel == 1)
    {
        /* Keep existing monochrome mapping: source 1 -> black. */
        return (sum_bw * 2 >= count) ? 0x0000 : 0xFFFF;
    }

    uint16_t r5 = (uint16_t)((sum_r + (count / 2u)) / count);
    uint16_t g6 = (uint16_t)((sum_g + (count / 2u)) / count);
    uint16_t b5 = (uint16_t)((sum_b + (count / 2u)) / count);
    return (uint16_t)((r5 << 11) | (g6 << 5) | b5);
}

static int tile_hash_equal(tile_hash_t a, tile_hash_t b)
{
    return a.h1 == b.h1 && a.h2 == b.h2;
}

static tile_hash_t tile_sparse_nn_hash(const uint8_t *src, uint32_t source_mask,
                                       unsigned int tile_x0, unsigned int tile_y0,
                                       unsigned int tile_x1, unsigned int tile_y1,
                                       unsigned int base_w, unsigned int base_h)
{
    tile_hash_t hash = {
        1469598103934665603ull,
        1099511628211ull,
    };

    for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
    {
        unsigned int dx = tile_x0 + ((dy + tile_x0 + tile_y0) & 1u);
        for (; dx < tile_x1; dx += 2)
        {
            uint16_t out565 = output_pixel_to_rgb565(src, source_mask, dx, dy, base_w, base_h);
            hash.h1 ^= (uint64_t)out565;
            hash.h1 *= 1099511628211ull;

            hash.h2 ^= (uint64_t)(out565 + (dx << 3) + (dy << 7));
            hash.h2 *= 14029467366897019727ull;
        }
    }

    return hash;
}

static tile_hash_t tile_sparse_source_hash(const uint8_t *src, uint32_t source_mask,
                                           unsigned int tile_x0, unsigned int tile_y0,
                                           unsigned int tile_x1, unsigned int tile_y1,
                                           unsigned int base_w, unsigned int base_h,
                                           unsigned int sample_step)
{
    tile_hash_t hash = {
        1469598103934665603ull,
        1099511628211ull,
    };

    if (vnc_rotate == 0 && bits_per_pixel != 1)
    {
        const unsigned int src_x_step = sample_step * downsample_factor;
        const unsigned int byte_step = src_x_step * bytespp;

        for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
        {
            unsigned int dx = tile_x0 + ((dy + tile_x0 + tile_y0) & 1u);
            unsigned int sy = dy * downsample_factor;
            unsigned int sx = dx * downsample_factor;
            const uint8_t *pixel_ptr = src + ((sy * fb_xres + sx) * bytespp);

            for (; dx < tile_x1; dx += sample_step, pixel_ptr += byte_step)
            {
                uint32_t sample;
                if (bytespp == 4)
                    sample = *(const uint32_t *)pixel_ptr;
                else if (bytespp == 2)
                    sample = *(const uint16_t *)pixel_ptr;
                else if (bytespp == 3)
                    sample = (uint32_t)pixel_ptr[0] |
                             ((uint32_t)pixel_ptr[1] << 8) |
                             ((uint32_t)pixel_ptr[2] << 16);
                else
                    sample = pixel_ptr[0];

                sample &= source_mask;

                hash.h1 ^= (uint64_t)sample;
                hash.h1 *= 1099511628211ull;

                hash.h2 ^= (uint64_t)(sample + (dx << 3) + (dy << 7));
                hash.h2 *= 14029467366897019727ull;
            }
        }

        return hash;
    }

    for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
    {
        unsigned int dx = tile_x0 + ((dy + tile_x0 + tile_y0) & 1u);
        for (; dx < tile_x1; dx += sample_step)
        {
            unsigned int base_x, base_y;
            if (vnc_rotate == 0)
            {
                base_x = dx;
                base_y = dy;
            }
            else
            {
                output_to_base(dx, dy, base_w, base_h, &base_x, &base_y);
            }

            uint32_t sample = read_source_at(src, source_mask,
                                             base_x * downsample_factor,
                                             base_y * downsample_factor);

            hash.h1 ^= (uint64_t)sample;
            hash.h1 *= 1099511628211ull;

            hash.h2 ^= (uint64_t)(sample + (dx << 3) + (dy << 7));
            hash.h2 *= 14029467366897019727ull;
        }
    }

    return hash;
}

static tile_hash_t tile_sparse_hash_from_snapshot(unsigned int tile_x0, unsigned int tile_y0,
                                                  unsigned int tile_x1, unsigned int tile_y1,
                                                  unsigned int sample_step)
{
    tile_hash_t hash = {
        1469598103934665603ull,
        1099511628211ull,
    };

    for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
    {
        unsigned int dx = tile_x0 + ((dy + tile_x0 + tile_y0) & 1u);
        for (; dx < tile_x1; dx += sample_step)
        {
            uint16_t out565 = relay_nn_snapshot[dy * relay_xres + dx];
            hash.h1 ^= (uint64_t)out565;
            hash.h1 *= 1099511628211ull;

            hash.h2 ^= (uint64_t)(out565 + (dx << 3) + (dy << 7));
            hash.h2 *= 14029467366897019727ull;
        }
    }

    return hash;
}

static unsigned int tile_cache_key(tile_hash_t hash, unsigned int width, unsigned int height)
{
    uint64_t k = hash.h1 ^ (hash.h2 * 0x9E3779B97F4A7C15ULL);
    k ^= ((uint64_t)width << 16) ^ (uint64_t)height;
    return (unsigned int)(k ^ (k >> 32));
}

static int tile_cache_entry_matches(int idx, tile_hash_t hash, unsigned int width, unsigned int height)
{
    const tile_cache_entry_t *e = &tile_cache[idx];
    return e->valid && e->width == width && e->height == height && tile_hash_equal(e->hash, hash);
}

static int tile_cache_find(tile_hash_t hash, unsigned int width, unsigned int height)
{
    if (tile_cache_map_capacity == 0)
        return -1;

    unsigned int mask = tile_cache_map_capacity - 1;
    unsigned int slot = tile_cache_key(hash, width, height) & mask;

    for (unsigned int probes = 0; probes < tile_cache_map_capacity; probes++)
    {
        uint8_t state = tile_cache_map_state[slot];
        if (state == CACHE_MAP_EMPTY)
            return -1;

        if (state == CACHE_MAP_OCCUPIED)
        {
            int idx = tile_cache_map_index[slot];
            if (idx >= 0 && (unsigned int)idx < tile_cache_capacity &&
                tile_cache_entry_matches(idx, hash, width, height))
            {
                return idx;
            }
        }

        slot = (slot + 1u) & mask;
    }

    return -1;
}

static void tile_cache_map_remove(tile_hash_t hash, unsigned int width, unsigned int height, int idx)
{
    if (tile_cache_map_capacity == 0)
        return;

    unsigned int mask = tile_cache_map_capacity - 1;
    unsigned int slot = tile_cache_key(hash, width, height) & mask;

    for (unsigned int probes = 0; probes < tile_cache_map_capacity; probes++)
    {
        uint8_t state = tile_cache_map_state[slot];
        if (state == CACHE_MAP_EMPTY)
            return;

        if (state == CACHE_MAP_OCCUPIED && tile_cache_map_index[slot] == idx)
        {
            tile_cache_map_state[slot] = CACHE_MAP_TOMBSTONE;
            tile_cache_map_index[slot] = -1;
            return;
        }

        slot = (slot + 1u) & mask;
    }
}

static void tile_cache_map_insert(tile_hash_t hash, unsigned int width, unsigned int height, int idx)
{
    if (tile_cache_map_capacity == 0)
        return;

    unsigned int mask = tile_cache_map_capacity - 1;
    unsigned int slot = tile_cache_key(hash, width, height) & mask;
    int first_tombstone = -1;

    for (unsigned int probes = 0; probes < tile_cache_map_capacity; probes++)
    {
        uint8_t state = tile_cache_map_state[slot];

        if (state == CACHE_MAP_EMPTY)
        {
            unsigned int target = first_tombstone >= 0 ? (unsigned int)first_tombstone : slot;
            tile_cache_map_state[target] = CACHE_MAP_OCCUPIED;
            tile_cache_map_index[target] = idx;
            return;
        }

        if (state == CACHE_MAP_TOMBSTONE)
        {
            if (first_tombstone < 0)
                first_tombstone = (int)slot;
        }
        else
        {
            int existing = tile_cache_map_index[slot];
            if (existing >= 0 && (unsigned int)existing < tile_cache_capacity &&
                tile_cache_entry_matches(existing, hash, width, height))
            {
                tile_cache_map_index[slot] = idx;
                return;
            }
        }

        slot = (slot + 1u) & mask;
    }

    if (first_tombstone >= 0)
    {
        tile_cache_map_state[(unsigned int)first_tombstone] = CACHE_MAP_OCCUPIED;
        tile_cache_map_index[(unsigned int)first_tombstone] = idx;
    }
}

static int tile_cache_find_slot_to_replace(void)
{
    int free_idx = -1;
    int lru_idx = 0;
    uint64_t lru_tick = UINT64_MAX;

    for (unsigned int i = 0; i < tile_cache_capacity; i++)
    {
        if (!tile_cache[i].valid)
        {
            free_idx = (int)i;
            break;
        }

        if (tile_cache[i].last_used_tick < lru_tick)
        {
            lru_tick = tile_cache[i].last_used_tick;
            lru_idx = (int)i;
        }
    }

    return free_idx >= 0 ? free_idx : lru_idx;
}

static void tile_cache_store(tile_hash_t hash, unsigned int width, unsigned int height,
                             const uint8_t *pixels)
{
    int idx = tile_cache_find(hash, width, height);
    if (idx < 0)
        idx = tile_cache_find_slot_to_replace();

    if (tile_cache[idx].valid && !tile_cache_entry_matches(idx, hash, width, height))
    {
        tile_cache_map_remove(tile_cache[idx].hash,
                              tile_cache[idx].width,
                              tile_cache[idx].height,
                              idx);
    }

    tile_cache[idx].valid = 1;
    tile_cache[idx].hash = hash;
    tile_cache[idx].width = (uint16_t)width;
    tile_cache[idx].height = (uint16_t)height;
    tile_cache[idx].last_used_tick = ++cache_use_tick;

    size_t bytes = width * height * OUTPUT_BYTES_PER_PIXEL;
    memcpy(tile_cache[idx].pixels, pixels, bytes);

    tile_cache_map_insert(hash, width, height, idx);
}

static void tile_cache_touch(int idx)
{
    tile_cache[idx].last_used_tick = ++cache_use_tick;
}

static int tile_cache_differs_from_output(int cache_idx, unsigned int tile_x0, unsigned int tile_y0)
{
    const tile_cache_entry_t *entry = &tile_cache[cache_idx];
    unsigned int width = entry->width;
    unsigned int height = entry->height;

    for (unsigned int dy = 0; dy < height; dy++)
    {
        unsigned int out_row = (tile_y0 + dy) * relay_xres + tile_x0;
        const uint8_t *cached_row = entry->pixels + dy * width * OUTPUT_BYTES_PER_PIXEL;
        const uint8_t *out_row_ptr = vnc_prevbuf + out_row * OUTPUT_BYTES_PER_PIXEL;
        if (memcmp(out_row_ptr, cached_row, width * OUTPUT_BYTES_PER_PIXEL) != 0)
            return 1;
    }

    return 0;
}

static uint64_t time_now_us(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000000ULL + (uint64_t)tv.tv_usec;
}

static uint64_t probe_fb_sequential_read(const uint8_t *src, size_t bytes)
{
    uint64_t acc = 0;
    for (size_t i = 0; i < bytes; i++)
        acc += src[i];
    return acc;
}

static uint64_t probe_fb_detect_pattern_read(const uint8_t *src,
                                             uint32_t source_mask,
                                             unsigned int base_w,
                                             unsigned int base_h,
                                             uint64_t *sample_count)
{
    uint64_t acc = 0;
    uint64_t samples = 0;

    for (unsigned int ty = 0; ty < relay_tile_rows; ty++)
    {
        for (unsigned int tx = 0; tx < relay_tile_cols; tx++)
        {
            unsigned int tile_x0 = tx * DIRTY_TILE_SIZE;
            unsigned int tile_y0 = ty * DIRTY_TILE_SIZE;
            unsigned int tile_x1 = tile_x0 + DIRTY_TILE_SIZE;
            unsigned int tile_y1 = tile_y0 + DIRTY_TILE_SIZE;
            if (tile_x1 > relay_xres)
                tile_x1 = relay_xres;
            if (tile_y1 > relay_yres)
                tile_y1 = relay_yres;

            for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
            {
                unsigned int dx = tile_x0 + ((dy + tile_x0 + tile_y0) & 1u);
                for (; dx < tile_x1; dx += 2)
                {
                    unsigned int base_x, base_y;
                    output_to_base(dx, dy, base_w, base_h, &base_x, &base_y);
                    uint32_t sample = read_source_at(src, source_mask,
                                                     base_x * downsample_factor,
                                                     base_y * downsample_factor);
                    acc += sample;
                    samples++;
                }
            }
        }
    }

    *sample_count = samples;
    return acc;
}

static void *fb_shadow_copy_main(void *opaque)
{
    fb_shadow_copy_job_t *job = (fb_shadow_copy_job_t *)opaque;
    memcpy(job->dst, job->src, job->bytes);
    return NULL;
}

static void build_relay_nn_snapshot(const uint8_t *src, uint32_t source_mask,
                                    unsigned int base_w, unsigned int base_h)
{
    for (unsigned int dy = 0; dy < relay_yres; dy++)
    {
        uint16_t *row = relay_nn_snapshot + (dy * relay_xres);
        for (unsigned int dx = 0; dx < relay_xres; dx++)
        {
            row[dx] = output_pixel_to_rgb565(src, source_mask, dx, dy, base_w, base_h);
        }
    }
}

static void tile_build_queue_push(unsigned int width, unsigned int height,
                                  unsigned int tile_x0, unsigned int tile_y0,
                                  unsigned int base_w, unsigned int base_h)
{
    if (tile_build_queue_count >= tile_build_queue_capacity)
        return;

    unsigned int idx = tile_build_queue_head;
    for (unsigned int i = 0; i < tile_build_queue_count; i++)
    {
        const tile_build_task_t *t = &tile_build_queue[idx];
        if (t->tile_x0 == tile_x0 && t->tile_y0 == tile_y0)
            return;
        idx = (idx + 1) % tile_build_queue_capacity;
    }

    tile_build_task_t *task = &tile_build_queue[tile_build_queue_tail];
    task->width = (uint16_t)width;
    task->height = (uint16_t)height;
    task->tile_x0 = (uint16_t)tile_x0;
    task->tile_y0 = (uint16_t)tile_y0;
    task->base_w = (uint16_t)base_w;
    task->base_h = (uint16_t)base_h;

    tile_build_queue_tail = (tile_build_queue_tail + 1) % tile_build_queue_capacity;
    tile_build_queue_count++;
}

static int tile_build_queue_pop(tile_build_task_t *out)
{
    if (tile_build_queue_count == 0)
        return 0;

    *out = tile_build_queue[tile_build_queue_head];
    tile_build_queue_head = (tile_build_queue_head + 1) % tile_build_queue_capacity;
    tile_build_queue_count--;
    return 1;
}

static void process_tile_build_queue(const uint8_t *src, uint32_t source_mask)
{
    uint8_t tilebuf[DIRTY_TILE_SIZE * DIRTY_TILE_SIZE * OUTPUT_BYTES_PER_PIXEL];

    while (tile_build_queue_count > 0)
    {
        tile_build_task_t task;
        if (!tile_build_queue_pop(&task))
            break;

        unsigned int tile_x1 = task.tile_x0 + task.width;
        unsigned int tile_y1 = task.tile_y0 + task.height;
        tile_hash_t hash;
        if (use_sequential_dump)
        {
            hash = tile_sparse_hash_from_snapshot(task.tile_x0, task.tile_y0,
                                                  tile_x1, tile_y1, 2);
        }
        else
        {
            hash = tile_sparse_nn_hash(src, source_mask,
                                       task.tile_x0, task.tile_y0,
                                       tile_x1, tile_y1,
                                       task.base_w, task.base_h);
        }

        if (tile_cache_find(hash, task.width, task.height) >= 0)
            continue;

        for (unsigned int y = 0; y < task.height; y++)
        {
            for (unsigned int x = 0; x < task.width; x++)
            {
                uint16_t px = output_pixel_to_rgb565_averaged(src, source_mask,
                                                              task.tile_x0 + x,
                                                              task.tile_y0 + y,
                                                              task.base_w,
                                                              task.base_h);
                size_t off = (y * task.width + x) * OUTPUT_BYTES_PER_PIXEL;
                tilebuf[off + 0] = (uint8_t)(px & 0xFF);
                tilebuf[off + 1] = (uint8_t)((px >> 8) & 0xFF);
            }
        }

        tile_cache_store(hash, task.width, task.height, tilebuf);
    }
}

static int tile_needs_update_sparse(const uint8_t *src, uint32_t source_mask,
                                    unsigned int tile_x0, unsigned int tile_y0,
                                    unsigned int tile_x1, unsigned int tile_y1,
                                    unsigned int base_w, unsigned int base_h)
{
    const int rbytespp = OUTPUT_BYTES_PER_PIXEL;
    unsigned int w = tile_x1 - tile_x0;
    unsigned int h = tile_y1 - tile_y0;
    if (w == 0 || h == 0)
        return 0;

    for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
    {
        /* Checkerboard: sample every other output pixel only. */
        unsigned int dx = tile_x0 + ((dy + tile_x0 + tile_y0) & 1u);
        for (; dx < tile_x1; dx += 2)
        {
            uint16_t out565 = output_pixel_to_rgb565(src, source_mask, dx, dy, base_w, base_h);
            uint8_t out[2] = {
                (uint8_t)(out565 & 0xFF),
                (uint8_t)((out565 >> 8) & 0xFF),
            };
            unsigned int out_index = (dy * relay_xres + dx) * rbytespp;
            if (memcmp(vnc_prevbuf + out_index, out, rbytespp) != 0)
                return 1;
        }
    }
    return 0;
}

typedef struct tile_worker_args_t
{
    const uint8_t *src;
    uint32_t source_mask;
    unsigned int base_w;
    unsigned int base_h;
    unsigned int tile_row_start;
    unsigned int tile_row_end;
    int min_i;
    int min_j;
    int max_i;
    int max_j;
} tile_worker_args_t;

static void draw_debug_tile_overlay(tile_worker_args_t *args,
                                    unsigned int tile_index,
                                    unsigned int tile_x0,
                                    unsigned int tile_y0,
                                    unsigned int tile_x1,
                                    unsigned int tile_y1,
                                    uint16_t border_color)
{
    const int rbytespp = OUTPUT_BYTES_PER_PIXEL;
    const uint16_t marker_magenta = 0xF81F;
    const unsigned int marker_inset = 2;

    if (tile_x1 <= tile_x0 || tile_y1 <= tile_y0)
        return;

    uint8_t c0 = (uint8_t)(border_color & 0xFF);
    uint8_t c1 = (uint8_t)((border_color >> 8) & 0xFF);

    for (unsigned int x = tile_x0; x < tile_x1; x++)
    {
        unsigned int top = (tile_y0 * relay_xres + x) * rbytespp;
        unsigned int bottom = ((tile_y1 - 1) * relay_xres + x) * rbytespp;
        vnc_prevbuf[top + 0] = c0;
        vnc_prevbuf[top + 1] = c1;
        vncbuf[top + 0] = c0;
        vncbuf[top + 1] = c1;
        vnc_prevbuf[bottom + 0] = c0;
        vnc_prevbuf[bottom + 1] = c1;
        vncbuf[bottom + 0] = c0;
        vncbuf[bottom + 1] = c1;
    }

    for (unsigned int y = tile_y0; y < tile_y1; y++)
    {
        unsigned int left = (y * relay_xres + tile_x0) * rbytespp;
        unsigned int right = (y * relay_xres + (tile_x1 - 1)) * rbytespp;
        vnc_prevbuf[left + 0] = c0;
        vnc_prevbuf[left + 1] = c1;
        vncbuf[left + 0] = c0;
        vncbuf[left + 1] = c1;
        vnc_prevbuf[right + 0] = c0;
        vnc_prevbuf[right + 1] = c1;
        vncbuf[right + 0] = c0;
        vncbuf[right + 1] = c1;
    }

    unsigned int x_min = tile_x0 + marker_inset;
    unsigned int x_max = tile_x1 - 1 - marker_inset;
    unsigned int y_min = tile_y0 + marker_inset;
    unsigned int y_max = tile_y1 - 1 - marker_inset;

    if (x_min >= tile_x1)
        x_min = tile_x0;
    if (x_max < tile_x0)
        x_max = tile_x1 - 1;
    if (y_min >= tile_y1)
        y_min = tile_y0;
    if (y_max < tile_y0)
        y_max = tile_y1 - 1;

    unsigned int marker_corner = tile_debug_corner_state[tile_index] & 0x3u;
    unsigned int marker_x = (marker_corner == 0u || marker_corner == 3u) ? x_min : x_max;
    unsigned int marker_y = (marker_corner == 0u || marker_corner == 1u) ? y_min : y_max;
    tile_debug_corner_state[tile_index] = (uint8_t)((tile_debug_corner_state[tile_index] + 1u) & 0x3u);

    uint8_t m0 = (uint8_t)(marker_magenta & 0xFF);
    uint8_t m1 = (uint8_t)((marker_magenta >> 8) & 0xFF);
    unsigned int marker = (marker_y * relay_xres + marker_x) * rbytespp;
    vnc_prevbuf[marker + 0] = m0;
    vnc_prevbuf[marker + 1] = m1;
    vncbuf[marker + 0] = m0;
    vncbuf[marker + 1] = m1;

    if ((int)tile_x0 < args->min_i)
        args->min_i = (int)tile_x0;
    if ((int)(tile_x1 - 1) > args->max_i)
        args->max_i = (int)(tile_x1 - 1);
    if ((int)tile_y0 < args->min_j)
        args->min_j = (int)tile_y0;
    if ((int)(tile_y1 - 1) > args->max_j)
        args->max_j = (int)(tile_y1 - 1);
}

static void process_dirty_tile_rows(tile_worker_args_t *args)
{
    const int rbytespp = OUTPUT_BYTES_PER_PIXEL;
    const uint16_t border_red = 0xF800;
    const uint16_t border_green = 0x07E0;

    args->min_i = 9999;
    args->min_j = 9999;
    args->max_i = -1;
    args->max_j = -1;

    for (unsigned int ty = args->tile_row_start; ty < args->tile_row_end; ty++)
    {
        for (unsigned int tx = 0; tx < relay_tile_cols; tx++)
        {
            unsigned int tile_index = ty * relay_tile_cols + tx;
            if (!tile_dirty[tile_index])
                continue;
            if (tile_copy_source_index[tile_index] >= 0)
                continue;
            int render_from_cache = tile_render_from_cache[tile_index] != 0;
            int cache_idx = tile_cache_index[tile_index];

            unsigned int tile_x0 = tx * DIRTY_TILE_SIZE;
            unsigned int tile_y0 = ty * DIRTY_TILE_SIZE;
            unsigned int tile_x1 = tile_x0 + DIRTY_TILE_SIZE;
            unsigned int tile_y1 = tile_y0 + DIRTY_TILE_SIZE;
            if (tile_x1 > relay_xres)
                tile_x1 = relay_xres;
            if (tile_y1 > relay_yres)
                tile_y1 = relay_yres;

            if (render_from_cache && cache_idx >= 0)
            {
                const tile_cache_entry_t *entry = &tile_cache[cache_idx];
                unsigned int width = entry->width;
                unsigned int height = entry->height;

                for (unsigned int dy = 0; dy < height; dy++)
                {
                    unsigned int out_row = (tile_y0 + dy) * relay_xres + tile_x0;
                    uint8_t *dst_prev = vnc_prevbuf + out_row * OUTPUT_BYTES_PER_PIXEL;
                    uint8_t *dst_vnc = vncbuf + out_row * OUTPUT_BYTES_PER_PIXEL;
                    const uint8_t *src_cached = entry->pixels + dy * width * OUTPUT_BYTES_PER_PIXEL;

                    if (memcmp(dst_prev, src_cached, width * OUTPUT_BYTES_PER_PIXEL) != 0)
                    {
                        memcpy(dst_prev, src_cached, width * OUTPUT_BYTES_PER_PIXEL);
                        memcpy(dst_vnc, src_cached, width * OUTPUT_BYTES_PER_PIXEL);

                        if ((int)tile_x0 < args->min_i)
                            args->min_i = (int)tile_x0;
                        if ((int)(tile_x0 + width - 1) > args->max_i)
                            args->max_i = (int)(tile_x0 + width - 1);
                        if ((int)(tile_y0 + dy) < args->min_j)
                            args->min_j = (int)(tile_y0 + dy);
                        if ((int)(tile_y0 + dy) > args->max_j)
                            args->max_j = (int)(tile_y0 + dy);
                    }
                }

#if DEBUG_TILE_MODE
                draw_debug_tile_overlay(args, tile_index, tile_x0, tile_y0, tile_x1, tile_y1, border_green);
#endif

                continue;
            }

            for (unsigned int dy = tile_y0; dy < tile_y1; dy++)
            {
                for (unsigned int dx = tile_x0; dx < tile_x1; dx++)
                {
                    uint16_t out565;
                    if (use_sequential_dump)
                    {
                        out565 = relay_nn_snapshot[dy * relay_xres + dx];
                    }
                    else
                    {
                        out565 = output_pixel_to_rgb565(args->src, args->source_mask, dx, dy,
                                                        args->base_w, args->base_h);
                    }

                    uint8_t out[2] = {
                        (uint8_t)(out565 & 0xFF),
                        (uint8_t)((out565 >> 8) & 0xFF),
                    };

                    unsigned int out_index = (dy * relay_xres + dx) * rbytespp;
                    if (memcmp(vnc_prevbuf + out_index, out, rbytespp) != 0)
                    {
                        memcpy(vnc_prevbuf + out_index, out, rbytespp);
                        memcpy(vncbuf + out_index, out, rbytespp);

                        if ((int)dx < args->min_i)
                            args->min_i = (int)dx;
                        if ((int)dx > args->max_i)
                            args->max_i = (int)dx;
                        if ((int)dy < args->min_j)
                            args->min_j = (int)dy;
                        if ((int)dy > args->max_j)
                            args->max_j = (int)dy;
                    }
                }
            }

#if DEBUG_TILE_MODE
            {
                uint16_t border_color = render_from_cache ? border_green : border_red;
                draw_debug_tile_overlay(args, tile_index, tile_x0, tile_y0, tile_x1, tile_y1, border_color);
            }
#endif
        }
    }
}

static void *tile_worker_main(void *opaque)
{
    tile_worker_args_t *args = (tile_worker_args_t *)opaque;
    process_dirty_tile_rows(args);
    return NULL;
}

static void wait_for_vsync_if_supported(void)
{
    if (!vsync_wait_enabled)
        return;

#ifdef FBIO_WAITFORVSYNC
    int zero = 0;
    if (ioctl(fbfd, FBIO_WAITFORVSYNC, &zero) == 0)
        return;

    /* If unsupported, disable retries to avoid per-frame ioctl overhead. */
    if (errno == ENOTTY || errno == EINVAL || errno == ENOSYS || errno == EOPNOTSUPP)
    {
        info_print("FBIO_WAITFORVSYNC not supported on %s; continuing without vsync sync\n", fb_device);
        vsync_wait_enabled = 0;
        return;
    }

    if (errno == EINTR)
        return;

    error_print("FBIO_WAITFORVSYNC failed (%d); disabling vsync sync\n", errno);
    vsync_wait_enabled = 0;
#else
    info_print("FBIO_WAITFORVSYNC is unavailable at build time; continuing without vsync sync\n");
    vsync_wait_enabled = 0;
#endif
}

static unsigned int copy_anchor_key(tile_hash_t hash)
{
    uint64_t k = hash.h1 ^ (hash.h2 * 0x9E3779B97F4A7C15ULL);
    return (unsigned int)(k ^ (k >> 32));
}

static void tile_index_bounds(unsigned int tile_index,
                              unsigned int *tile_x0,
                              unsigned int *tile_y0,
                              unsigned int *tile_x1,
                              unsigned int *tile_y1)
{
    unsigned int tx = tile_index % relay_tile_cols;
    unsigned int ty = tile_index / relay_tile_cols;

    *tile_x0 = tx * DIRTY_TILE_SIZE;
    *tile_y0 = ty * DIRTY_TILE_SIZE;
    *tile_x1 = *tile_x0 + DIRTY_TILE_SIZE;
    *tile_y1 = *tile_y0 + DIRTY_TILE_SIZE;
    if (*tile_x1 > relay_xres)
        *tile_x1 = relay_xres;
    if (*tile_y1 > relay_yres)
        *tile_y1 = relay_yres;
}

static void build_copyrect_plan(void)
{
    memset(tile_copy_source_index, 0xFF, relay_tile_count * sizeof(int));
    memset(copy_anchor_map_slot, 0xFF, copy_anchor_map_capacity * sizeof(int));

    for (unsigned int i = 0; i < relay_tile_count; i++)
    {
        if (tile_dirty[i])
            continue;

        tile_hash_t hash = tile_frame_hash[i];
        unsigned int slot = copy_anchor_key(hash) & (copy_anchor_map_capacity - 1);
        for (;;)
        {
            int existing = copy_anchor_map_slot[slot];
            if (existing < 0)
            {
                copy_anchor_map_slot[slot] = (int)i;
                break;
            }

            if (tile_hash_equal(tile_frame_hash[(unsigned int)existing], hash))
                break;

            slot = (slot + 1u) & (copy_anchor_map_capacity - 1);
        }
    }

    for (unsigned int i = 0; i < relay_tile_count; i++)
    {
        if (!tile_dirty[i])
            continue;

        tile_hash_t hash = tile_frame_hash[i];
        unsigned int slot = copy_anchor_key(hash) & (copy_anchor_map_capacity - 1);

        for (;;)
        {
            int existing = copy_anchor_map_slot[slot];
            if (existing < 0)
                break;

            unsigned int src_idx = (unsigned int)existing;
            if (src_idx != i && tile_hash_equal(tile_frame_hash[src_idx], hash))
            {
                unsigned int src_x0, src_y0, src_x1, src_y1;
                unsigned int dst_x0, dst_y0, dst_x1, dst_y1;
                tile_index_bounds(src_idx, &src_x0, &src_y0, &src_x1, &src_y1);
                tile_index_bounds(i, &dst_x0, &dst_y0, &dst_x1, &dst_y1);
                if ((src_x1 - src_x0) == (dst_x1 - dst_x0) &&
                    (src_y1 - src_y0) == (dst_y1 - dst_y0))
                {
                    tile_copy_source_index[i] = (int)src_idx;
                }
                break;
            }

            slot = (slot + 1u) & (copy_anchor_map_capacity - 1);
        }
    }
}

static void mark_dirty_tiles_modified(void)
{
    unsigned int dirty_tiles = 0;
    unsigned int dirty_rects = 0;
    unsigned int copy_tiles = 0;

    for (unsigned int i = 0; i < relay_tile_count; i++)
    {
        if (!tile_dirty[i])
            continue;
        int src = tile_copy_source_index[i];
        if (src < 0)
            continue;

        unsigned int src_x0, src_y0, src_x1, src_y1;
        unsigned int dst_x0, dst_y0, dst_x1, dst_y1;
        tile_index_bounds((unsigned int)src, &src_x0, &src_y0, &src_x1, &src_y1);
        tile_index_bounds(i, &dst_x0, &dst_y0, &dst_x1, &dst_y1);

        unsigned int copy_w = dst_x1 - dst_x0;
        unsigned int copy_h = dst_y1 - dst_y0;
        for (unsigned int row = 0; row < copy_h; row++)
        {
            unsigned int src_row = (src_y0 + row) * relay_xres + src_x0;
            unsigned int dst_row = (dst_y0 + row) * relay_xres + dst_x0;
            uint8_t *src_prev = vnc_prevbuf + src_row * OUTPUT_BYTES_PER_PIXEL;
            uint8_t *dst_prev = vnc_prevbuf + dst_row * OUTPUT_BYTES_PER_PIXEL;
            uint8_t *src_vnc = vncbuf + src_row * OUTPUT_BYTES_PER_PIXEL;
            uint8_t *dst_vnc = vncbuf + dst_row * OUTPUT_BYTES_PER_PIXEL;
            memcpy(dst_prev, src_prev, copy_w * OUTPUT_BYTES_PER_PIXEL);
            memcpy(dst_vnc, src_vnc, copy_w * OUTPUT_BYTES_PER_PIXEL);
        }

        rfbScheduleCopyRect(server,
                            (int)dst_x0, (int)dst_y0, (int)dst_x1, (int)dst_y1,
                            (int)dst_x0 - (int)src_x0,
                            (int)dst_y0 - (int)src_y0);
        copy_tiles++;
    }

    for (unsigned int ty = 0; ty < relay_tile_rows; ty++)
    {
        unsigned int tx = 0;
        while (tx < relay_tile_cols)
        {
            while (tx < relay_tile_cols)
            {
                unsigned int tile_index = ty * relay_tile_cols + tx;
                if (tile_dirty[tile_index] && tile_copy_source_index[tile_index] < 0)
                    break;
                tx++;
            }

            if (tx >= relay_tile_cols)
                break;

            unsigned int run_start = tx;
            while (tx < relay_tile_cols)
            {
                unsigned int tile_index = ty * relay_tile_cols + tx;
                if (!tile_dirty[tile_index] || tile_copy_source_index[tile_index] >= 0)
                    break;
                dirty_tiles++;
                tx++;
            }
            unsigned int run_end = tx;

            unsigned int x0 = run_start * DIRTY_TILE_SIZE;
            unsigned int x1 = run_end * DIRTY_TILE_SIZE;
            unsigned int y0 = ty * DIRTY_TILE_SIZE;
            unsigned int y1 = y0 + DIRTY_TILE_SIZE;

            if (x1 > relay_xres)
                x1 = relay_xres;
            if (y1 > relay_yres)
                y1 = relay_yres;

            rfbMarkRectAsModified(server, x0, y0, x1, y1);
            dirty_rects++;
        }
    }

    if (dirty_tiles > 0 || copy_tiles > 0)
    {
        debug_print("Dirty tiles: %u, modified rects: %u, copyrect tiles: %u\n",
                    dirty_tiles, dirty_rects, copy_tiles);
    }
}

static void update_screen(void)
{
    uint64_t fb_shadow_copy_start_us;
    uint64_t fb_shadow_copy_elapsed_us = 0;
    uint64_t fb_dump_start_us;
    uint64_t fb_dump_elapsed_us = 0;
    uint64_t fb_detect_start_us;
    uint64_t fb_detect_elapsed_us;
    uint64_t fb_render_start_us;
    uint64_t fb_render_elapsed_us;
    uint64_t fb_cache_build_start_us;
    uint64_t fb_cache_build_elapsed_us;
    static unsigned int fb_probe_frame_counter = 0;
    static uint64_t detect_frame_counter = 0;

#ifdef LOG_FPS
    if (verbose)
    {
        static int frames = 0;
        frames++;
        if (timeToLogFPS())
        {
            double fps = frames / LOG_TIME;
            info_print("  fps: %f\n", fps);
            frames = 0;
        }
    }
#endif

    wait_for_vsync_if_supported();

    const uint8_t *src = (const uint8_t *)fbmmap;
    const uint32_t source_mask = bits_per_pixel >= 32 ? 0xFFFFFFFFu : ((1u << bits_per_pixel) - 1u);

    if (use_shadow_copy)
    {
        fb_shadow_copy_start_us = time_now_us();

        if (!fb_shadow_initialized)
        {
            memcpy(fb_shadow_front, fbmmap, frame_size);
            fb_shadow_initialized = 1;
        }

        if (fb_shadow_copy_inflight)
        {
            pthread_join(fb_shadow_copy_thread, NULL);
            fb_shadow_copy_inflight = 0;

            uint8_t *tmp = fb_shadow_front;
            fb_shadow_front = fb_shadow_back;
            fb_shadow_back = tmp;
        }

        fb_shadow_copy_elapsed_us = time_now_us() - fb_shadow_copy_start_us;
        src = fb_shadow_front;

        fb_shadow_copy_job.src = (const uint8_t *)fbmmap;
        fb_shadow_copy_job.dst = fb_shadow_back;
        fb_shadow_copy_job.bytes = frame_size;
        if (pthread_create(&fb_shadow_copy_thread, NULL, fb_shadow_copy_main, &fb_shadow_copy_job) == 0)
        {
            fb_shadow_copy_inflight = 1;
        }
        else
        {
            memcpy(fb_shadow_back, fbmmap, frame_size);
            uint8_t *tmp = fb_shadow_front;
            fb_shadow_front = fb_shadow_back;
            fb_shadow_back = tmp;
            fb_shadow_copy_inflight = 0;
        }
    }

    unsigned int base_w = fb_xres / downsample_factor;
    unsigned int base_h = fb_yres / downsample_factor;
    if (base_w == 0)
        base_w = 1;
    if (base_h == 0)
        base_h = 1;

    detect_frame_counter++;
    int verify_detect_frame =
        detect_verify_interval > 0 &&
        ((detect_frame_counter % detect_verify_interval) == 0);
    unsigned int detect_step = verify_detect_frame ? 2u : detect_sample_step;

    for (unsigned int i = 0; i < relay_tile_count; i++)
    {
        tile_render_from_cache[i] = 0;
        tile_cache_index[i] = -1;
    }

    if (use_sequential_dump)
    {
        fb_dump_start_us = time_now_us();
        build_relay_nn_snapshot(src, source_mask, base_w, base_h);
        fb_dump_elapsed_us = time_now_us() - fb_dump_start_us;
    }

    fb_detect_start_us = time_now_us();

    for (unsigned int ty = 0; ty < relay_tile_rows; ty++)
    {
        for (unsigned int tx = 0; tx < relay_tile_cols; tx++)
        {
            unsigned int tile_index = ty * relay_tile_cols + tx;
            unsigned int tile_x0 = tx * DIRTY_TILE_SIZE;
            unsigned int tile_y0 = ty * DIRTY_TILE_SIZE;
            unsigned int tile_x1 = tile_x0 + DIRTY_TILE_SIZE;
            unsigned int tile_y1 = tile_y0 + DIRTY_TILE_SIZE;
            if (tile_x1 > relay_xres)
                tile_x1 = relay_xres;
            if (tile_y1 > relay_yres)
                tile_y1 = relay_yres;

            unsigned int tile_w = tile_x1 - tile_x0;
            unsigned int tile_h = tile_y1 - tile_y0;
            tile_hash_t hash;
            if (use_sequential_dump)
            {
                hash = tile_sparse_hash_from_snapshot(tile_x0, tile_y0,
                                                      tile_x1, tile_y1,
                                                      detect_step);
            }
            else
            {
                hash = tile_sparse_source_hash(src, source_mask,
                                               tile_x0, tile_y0,
                                               tile_x1, tile_y1,
                                               base_w, base_h,
                                               detect_step);
            }
            tile_frame_hash[tile_index] = hash;
            int frame_hash_changed =
                force_full_tile_refresh ||
                !tile_prev_frame_hash_valid[tile_index] ||
                !tile_hash_equal(tile_prev_frame_hash[tile_index], hash);
            tile_prev_frame_hash[tile_index] = hash;
            tile_prev_frame_hash_valid[tile_index] = 1;
            int cache_idx = -1;
            int hash_unchanged_for_position =
                !force_full_tile_refresh &&
                tile_last_served_valid[tile_index] &&
                tile_hash_equal(tile_last_served_hash[tile_index], hash);

            if (hash_unchanged_for_position)
            {
                tile_dirty[tile_index] = 0;
            }
            else
            {
                tile_dirty[tile_index] = frame_hash_changed;
            }

            int needs_cache_catchup =
                !force_full_tile_refresh &&
                !tile_dirty[tile_index] &&
                !tile_last_served_valid[tile_index];

            if (tile_dirty[tile_index] || needs_cache_catchup)
            {
                tile_hash_t cache_hash;
                if (use_sequential_dump)
                {
                    cache_hash = tile_sparse_hash_from_snapshot(tile_x0, tile_y0,
                                                                tile_x1, tile_y1,
                                                                2);
                }
                else
                {
                    cache_hash = tile_sparse_nn_hash(src, source_mask,
                                                     tile_x0, tile_y0,
                                                     tile_x1, tile_y1,
                                                     base_w, base_h);
                }

                cache_idx = tile_cache_find(cache_hash, tile_w, tile_h);

                if (!tile_dirty[tile_index] && needs_cache_catchup && cache_idx >= 0)
                    tile_dirty[tile_index] = 1;
            }

            if (tile_dirty[tile_index] && cache_idx >= 0)
            {
                tile_cache_touch(cache_idx);
                tile_cache_index[tile_index] = cache_idx;
                tile_render_from_cache[tile_index] = 1;
            }
            else if (tile_dirty[tile_index])
            {
                tile_build_queue_push(tile_w, tile_h,
                                      tile_x0, tile_y0,
                                      base_w, base_h);
            }

            if (tile_dirty[tile_index] && tile_render_from_cache[tile_index])
            {
                tile_last_served_hash[tile_index] = hash;
                tile_last_served_valid[tile_index] = 1;
            }
            else if (tile_dirty[tile_index])
            {
                tile_last_served_valid[tile_index] = 0;
            }
        }
    }

    fb_detect_elapsed_us = time_now_us() - fb_detect_start_us;

    build_copyrect_plan();

    for (unsigned int i = 0; i < relay_tile_count; i++)
    {
        if (tile_dirty[i] && tile_copy_source_index[i] >= 0)
            tile_last_served_valid[i] = 0;
    }

    force_full_tile_refresh = 0;

    tile_worker_args_t main_args = {
        .src = src,
        .source_mask = source_mask,
        .base_w = base_w,
        .base_h = base_h,
        .tile_row_start = 0,
        .tile_row_end = relay_tile_rows,
    };

    tile_worker_args_t worker_args = {
        .src = src,
        .source_mask = source_mask,
        .base_w = base_w,
        .base_h = base_h,
        .tile_row_start = relay_tile_rows / 2,
        .tile_row_end = relay_tile_rows,
    };

    pthread_t worker;
    int worker_started = 0;

    fb_render_start_us = time_now_us();

    if (relay_tile_rows > 1)
    {
        main_args.tile_row_end = relay_tile_rows / 2;
        if (main_args.tile_row_end == 0)
            main_args.tile_row_end = 1;
        worker_args.tile_row_start = main_args.tile_row_end;

        if (worker_args.tile_row_start < worker_args.tile_row_end)
        {
            if (pthread_create(&worker, NULL, tile_worker_main, &worker_args) == 0)
            {
                worker_started = 1;
            }
            else
            {
                main_args.tile_row_end = relay_tile_rows;
            }
        }
        else
        {
            main_args.tile_row_end = relay_tile_rows;
        }
    }

    process_dirty_tile_rows(&main_args);

    if (worker_started)
        pthread_join(worker, NULL);

    fb_render_elapsed_us = time_now_us() - fb_render_start_us;

    /* Build or refresh cache entries only after this frame's render pass,
     * so tile_cache_index selected above remains valid for the frame. */
    fb_cache_build_start_us = time_now_us();
    process_tile_build_queue(src, source_mask);
    fb_cache_build_elapsed_us = time_now_us() - fb_cache_build_start_us;

    if (verbose)
    {
        uint64_t fb_total_elapsed_us = fb_shadow_copy_elapsed_us + fb_dump_elapsed_us + fb_detect_elapsed_us + fb_render_elapsed_us + fb_cache_build_elapsed_us;
        info_print("  fb-read us: shadowwait=%llu dump=%llu detect=%llu render=%llu cachebuild=%llu total=%llu (detect_step=%u verify=%s)\n",
                   (unsigned long long)fb_shadow_copy_elapsed_us,
                   (unsigned long long)fb_dump_elapsed_us,
                   (unsigned long long)fb_detect_elapsed_us,
                   (unsigned long long)fb_render_elapsed_us,
                   (unsigned long long)fb_cache_build_elapsed_us,
               (unsigned long long)fb_total_elapsed_us,
               detect_step,
               verify_detect_frame ? "yes" : "no");

        fb_probe_frame_counter++;
        if ((fb_probe_frame_counter % 60u) == 0u)
        {
            uint64_t seq_start_us = time_now_us();
            const uint8_t *probe_src = (const uint8_t *)fbmmap;
            uint64_t seq_acc = probe_fb_sequential_read(probe_src, frame_size);
            uint64_t seq_elapsed_us = time_now_us() - seq_start_us;

            uint64_t detect_probe_samples = 0;
            uint64_t pat_start_us = time_now_us();
            uint64_t pat_acc = probe_fb_detect_pattern_read(probe_src, source_mask, base_w, base_h, &detect_probe_samples);
            uint64_t pat_elapsed_us = time_now_us() - pat_start_us;

            fb_probe_sink ^= (seq_acc + pat_acc + detect_probe_samples);

            double seq_mib = (double)frame_size / (1024.0 * 1024.0);
            double seq_sec = (double)seq_elapsed_us / 1000000.0;
            double seq_mib_s = seq_sec > 0.0 ? (seq_mib / seq_sec) : 0.0;

            info_print("  fb-probe us: seq=%llu (%.1f MiB/s) detect_pattern=%llu samples=%llu\n",
                       (unsigned long long)seq_elapsed_us,
                       seq_mib_s,
                       (unsigned long long)pat_elapsed_us,
                       (unsigned long long)detect_probe_samples);
        }
    }

    UNUSED(main_args);
    UNUSED(worker_args);
    mark_dirty_tiles_modified();
}

/*****************************************************************************/

void print_usage(char **argv)
{
    info_print("%s [-f device] [-p port] [-t touchscreen] [-m mouse] [-k keyboard] [-r rotation] [-R touchscreen rotation] [-F FPS] [-S factor] [-D step] [-V interval] [-Q] [-M] [-v] [-h]\n"
               "-p port: VNC port, default is 5900\n"
               "-f device: framebuffer device node, default is /dev/fb0\n"
               "-k device: keyboard device node (example: /dev/input/event0). If omitted/unavailable, tries /dev/uinput virtual keyboard\n"
               "-t device: touchscreen device node (example:/dev/input/event2)\n"
               "-m device: mouse device node (example:/dev/input/event2)\n"
               "-r degrees: framebuffer rotation, default is 0\n"
               "-R degrees: touchscreen rotation, default is same as framebuffer rotation\n"
               "-F FPS: Maximum target FPS, default is 10\n"
               "-S factor: Downsample factor for remote display (1=no downsample, 2, 4, ...), default is 4\n"
               "-D step: Detect sampling step in output pixels (even, >=2), default is 2\n"
               "-V interval: Full-verify interval in frames (0=disabled), default is 0\n"
               "-Q: Enable sequential relay snapshot A/B mode for detect and NN render\n"
               "-M: Enable raw framebuffer shadow-copy mode (copy once, process from RAM)\n"
               "-v: verbose\n"
               "-h: print this help\n",
               *argv);
}

int main(int argc, char **argv)
{
    if (argc > 1)
    {
        int i = 1;
        while (i < argc)
        {
            if (*argv[i] == '-')
            {
                switch (*(argv[i] + 1))
                {
                case 'h':
                    print_usage(argv);
                    exit(0);
                    break;
                case 'f':
                    i++;
                    if (argv[i])
                        strcpy(fb_device, argv[i]);
                    break;
                case 't':
                    i++;
                    if (argv[i])
                        strcpy(touch_device, argv[i]);
                    break;
                case 'm':
                    i++;
                    if (argv[i])
                        strcpy(mouse_device, argv[i]);
                    break;                    
                case 'k':
                    i++;
                    strcpy(kbd_device, argv[i]);
                    break;
                case 'p':
                    i++;
                    if (argv[i])
                        vnc_port = atoi(argv[i]);
                    break;
                case 'r':
                    i++;
                    if (argv[i])
                        vnc_rotate = atoi(argv[i]);
                    break;
                case 'R':
                    i++;
                    if (argv[i])
                        touch_rotate = atoi(argv[i]);
                    break;
               case 'F':
                    i++;
                    if (argv[i])
                        target_fps = atoi(argv[i]);
                    break;
                case 'S':
                    i++;
                    if (argv[i])
                    {
                        int factor = atoi(argv[i]);
                        if (factor < 1)
                        {
                            error_print("Invalid downsample factor %d; must be >= 1\n", factor);
                            exit(EXIT_FAILURE);
                        }
                        downsample_factor = (unsigned int)factor;
                    }
                    break;
                case 'D':
                    i++;
                    if (argv[i])
                    {
                        int step = atoi(argv[i]);
                        if (step < 2)
                        {
                            error_print("Invalid detect step %d; must be >= 2\n", step);
                            exit(EXIT_FAILURE);
                        }
                        if ((step & 1) != 0)
                            step += 1;
                        detect_sample_step = (unsigned int)step;
                    }
                    break;
                case 'V':
                    i++;
                    if (argv[i])
                    {
                        int interval = atoi(argv[i]);
                        if (interval < 0)
                        {
                            error_print("Invalid verify interval %d; must be >= 0\n", interval);
                            exit(EXIT_FAILURE);
                        }
                        detect_verify_interval = (unsigned int)interval;
                    }
                    break;
                case 'v':
                    verbose = 1;
                    break;
                case 'Q':
                    use_sequential_dump = 1;
                    break;
                case 'M':
                    use_shadow_copy = 1;
                    break;
                }
            }
            i++;
        }
    }

    if (touch_rotate < 0)
        touch_rotate = vnc_rotate;

    info_print("Initializing framebuffer device %s...\n", fb_device);
    init_fb();
    {
        int ret = init_kbd(kbd_device);
        if (!ret)
        {
            if (strlen(kbd_device) > 0)
                info_print("Keyboard device %s not available and no virtual fallback.\n", kbd_device);
            else
                info_print("No keyboard device and no virtual fallback.\n");
        }
    }

    rfbBool enable_touch = FALSE;
    rfbBool enable_mouse = FALSE;
    if(strlen(touch_device) > 0 && strlen(mouse_device) > 0)
    {
        error_print("It can't using both mouse and touch device.\n");
        exit(EXIT_FAILURE);
    }
    else if (strlen(touch_device) > 0)
    {
        // init touch only if there is a touch device defined
        int ret = init_touch(touch_device, touch_rotate);
        enable_touch = (ret > 0);
    }
    else if(strlen(mouse_device) > 0)
    {
        // init touch only if there is a mouse device defined
        int ret = init_mouse(mouse_device, touch_rotate);
        enable_mouse = (ret > 0);        
    }
    else
    {
        info_print("No touch or mouse device\n");
    }

    info_print("Initializing VNC server:\n");
    unsigned int log_width = fb_xres / downsample_factor;
    unsigned int log_height = fb_yres / downsample_factor;
    if (log_width == 0)
        log_width = 1;
    if (log_height == 0)
        log_height = 1;
    if (vnc_rotate == 90 || vnc_rotate == 270)
    {
        unsigned int tmp = log_width;
        log_width = log_height;
        log_height = tmp;
    }
    info_print("\twidth:  %d\n", (int)log_width);
    info_print("\theight: %d\n", (int)log_height);
    info_print("\tsource bpp: %d\n", (int)var_scrinfo.bits_per_pixel);
    info_print("\trelay bpp:  %d\n", 16);
    info_print("\tdownsample factor: %d\n", (int)downsample_factor);
    info_print("\tdetect sample step: %u\n", detect_sample_step);
    info_print("\tverify interval: %u\n", detect_verify_interval);
    info_print("\tsequential dump mode: %s\n", use_sequential_dump ? "enabled" : "disabled");
    info_print("\tshadow copy mode: %s\n", use_shadow_copy ? "enabled" : "disabled");
    info_print("	port:   %d\n", (int)vnc_port);
    info_print("	rotate: %d\n", (int)vnc_rotate);
    info_print("  mouse/touch rotate: %d\n", (int)touch_rotate);
    info_print("    target FPS: %d\n", (int)target_fps);
    init_fb_server(argc, argv, enable_touch, enable_mouse);

    /* Implement our own event loop to detect changes in the framebuffer. */
    while (1)
    {
        rfbRunEventLoop(server, 100 * 1000, TRUE);
        while (rfbIsActive(server))
        {
            if (server->clientHead != NULL)
                update_screen();

            if (target_fps > 0)
                usleep(1000 * 1000 / target_fps);
            else if (server->clientHead == NULL)
                usleep(100 * 1000);
        }
    }

    info_print("Cleaning up...\n");
    cleanup_fb();
    cleanup_kbd();
    cleanup_touch();
}
