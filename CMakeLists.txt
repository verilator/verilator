#*****************************************************************************
#
# DESCRIPTION: Script for build tool cmake on both unix and windows
#
#*****************************************************************************
#
# Copyright 2003-2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
#****************************************************************************/

cmake_minimum_required(VERSION 3.15)
cmake_policy(SET CMP0091 NEW) # Use MSVC_RUNTIME_LIBRARY to select the runtime
project(
    Verilator
    VERSION 5.032
    HOMEPAGE_URL https://verilator.org
    LANGUAGES CXX
)

# Set default build type to Release if not specified
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Build type" FORCE)
endif()

option(
    DEBUG_AND_RELEASE_AND_COVERAGE
    "Builds both the debug and release binaries, overriding CMAKE_BUILD_TYPE. Not supported under MSBuild."
)

find_package(Python3 COMPONENTS Interpreter)
set(PYTHON3 ${Python3_EXECUTABLE})
# See also CMake built-in; CMAKE_INSTALL_PREFIX is applied by the install command.
set(CMAKE_INSTALL_DATADIR .)
include(GNUInstallDirs)
include(CMakePackageConfigHelpers)
include(CheckStructHasMember)
include(ExternalProject)
include(FindThreads)

if(NOT WIN32)
    message(WARNING "CMake support on Linux/OSX is experimental.")
endif()

if(WIN32)
    if(DEFINED ENV{WIN_FLEX_BISON})
        set(WIN_FLEX_BISON "$ENV{WIN_FLEX_BISON}")
    endif()
    if(EXISTS ${WIN_FLEX_BISON})
        list(APPEND CMAKE_PREFIX_PATH ${WIN_FLEX_BISON})
    endif()
    if(NOT WIN_FLEX_BISON)
        message(
            FATAL_ERROR
            "Please install https://github.com/lexxmark/winflexbison and set WIN_FLEX_BISON environment variable. Please use install cmake target after a successful build."
        )
    endif()
    set(CMAKE_CXX_STANDARD 20)
endif()

set(OBJCACHE "" CACHE STRING "Path for ccache, auto-detected if empty")
option(OBJCACHE_ENABLED "Compile Verilator with ccache" ON)

if(OBJCACHE_ENABLED)
    if(OBJCACHE STREQUAL "")
        find_program(OBJCACHE_PATH ccache)
        if(OBJCACHE_PATH STREQUAL "OBJCACHE_PATH-NOTFOUND")
            set(OBJCACHE_PATH "")
        endif()
    else()
        set(OBJCACHE_PATH "${OBJCACHE}")
    endif()
    if(NOT OBJCACHE_PATH STREQUAL "")
        execute_process(
            COMMAND "${OBJCACHE_PATH}" --version
            OUTPUT_VARIABLE objcache_version
        )
        string(REGEX MATCH "[^\n\r]+" objcache_version "${objcache_version}")
        message(
            STATUS
            "Found ccache: ${OBJCACHE_PATH} (\"${objcache_version}\")"
        )
        set(CMAKE_CXX_COMPILER_LAUNCHER "${OBJCACHE_PATH}")
    endif()
endif()

find_package(BISON)
find_package(FLEX)

# Build
#set_property(GLOBAL PROPERTY JOB_POOLS one_job=1)

if(DEBUG_AND_RELEASE_AND_COVERAGE)
    if(CMAKE_GENERATOR MATCHES "^Visual Studio ")
        error("%Error: The DEBUG_AND_RELEASE_AND_COVERAGE option is not supported in MSBuild-based builds.")
    endif()
    set(saved_build_type ${CMAKE_BUILD_TYPE})
    set(CMAKE_BUILD_TYPE Debug)
    add_subdirectory(src build-Debug)
    set(CMAKE_BUILD_TYPE Release)
    add_subdirectory(src build-Release)
    set(CMAKE_BUILD_TYPE Coverage)
    add_subdirectory(src build-Coverage)
    set(CMAKE_BUILD_TYPE ${saved_build_type})
else()
    add_subdirectory(src)
endif()

# Configuration and Installation

set(PACKAGE_NAME ${PROJECT_NAME})
set(PACKAGE_VERSION ${PROJECT_VERSION})
set(CXX ${CMAKE_CXX_COMPILER})
set(AR ${CMAKE_AR})

configure_file(include/verilated_config.h.in include/verilated_config.h @ONLY)
configure_file(include/verilated.mk.in include/verilated.mk @ONLY)

install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/include/verilated_config.h
    DESTINATION include
)
install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/include/verilated.mk
    DESTINATION include
)

configure_package_config_file(
    verilator-config.cmake.in
    verilator-config.cmake
    INSTALL_DESTINATION .
)

install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/verilator-config.cmake
    DESTINATION .
)

configure_package_config_file(
    verilator-config-version.cmake.in
    verilator-config-version.cmake
    INSTALL_DESTINATION .
)

install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/verilator-config-version.cmake
    DESTINATION .
)

foreach(
    program
    verilator
    verilator_gantt
    verilator_ccache_report
    verilator_difftree
    verilator_profcfunc
    verilator_includer
)
    install(PROGRAMS bin/${program} TYPE BIN)
endforeach()

install(
    DIRECTORY examples
    TYPE DATA
    FILES_MATCHING
    PATTERN "examples/*/*.[chv]*"
    PATTERN "examples/*/Makefile*"
    PATTERN "examples/*/CMakeLists.txt"
)

install(
    DIRECTORY include
    TYPE DATA
    FILES_MATCHING
    PATTERN "include/verilated_config.h"
    PATTERN "include/*.[chv]"
    PATTERN "include/*.cpp"
    PATTERN "include/*.vlt"
    PATTERN "include/*.sv"
    PATTERN "include/gtkwave/*.[chv]*"
    PATTERN "include/vltstd/*.[chv]*"
)
