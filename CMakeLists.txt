CMAKE_MINIMUM_REQUIRED(VERSION 3.10)
PROJECT(framebuffer-vncserver C)

if(NOT CMAKE_CONFIGURATION_TYPES AND NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()


FILE(GLOB SOURCES src/*.c)
ADD_EXECUTABLE(framebuffer-vncserver ${SOURCES})
INSTALL(TARGETS framebuffer-vncserver RUNTIME DESTINATION bin)

find_package(Threads REQUIRED)

# LIBVNC
find_library(LIBVNC NAMES libvncserver vncserver)
target_link_libraries(framebuffer-vncserver ${LIBVNC})
target_link_libraries(framebuffer-vncserver ${CMAKE_THREAD_LIBS_INIT})


MESSAGE( STATUS "LIBVNC:         " ${LIBVNC} )
