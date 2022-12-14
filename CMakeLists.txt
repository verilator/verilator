#*****************************************************************************
# DESCRIPTION: Script for build tool cmake on both unix and windows
#
# This file is part of Verilator.
#
# Code available from: https://verilator.org
#
#*****************************************************************************
#
# Copyright 2003-2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
#****************************************************************************/

cmake_minimum_required(VERSION 3.15)
cmake_policy(SET CMP0091 NEW) # Use MSVC_RUNTIME_LIBRARY to select the runtime
project(Verilator
    VERSION 5.003
    HOMEPAGE_URL https://verilator.org
    LANGUAGES CXX
)

option(CMAKE_UNITY_BUILD
    "Builds concatenated source files, potentially sppeding up the build.")
option(DEBUG_AND_RELEASE_AND_COVERAGE
    "Builds both the debug and release binaries, overriding CMAKE_BUILD_TYPE. Not supported under MSBuild.")

set(CMAKE_INSTALL_DATADIR ${CMAKE_INSTALL_PREFIX})
include(GNUInstallDirs)
include(CMakePackageConfigHelpers)
include(CheckStructHasMember)
include(ExternalProject)

if (MSVC)
    if (DEFINED ENV{WIN_FLEX_BISON})
        set(WIN_FLEX_BISON "$ENV{WIN_FLEX_BISON}")
    endif()
    if (EXISTS ${WIN_FLEX_BISON})
        list(APPEND CMAKE_PREFIX_PATH ${WIN_FLEX_BISON})
    endif()
    if (NOT WIN_FLEX_BISON)
        message(FATAL_ERROR "Please install https://github.com/lexxmark/winflexbison and set WIN_FLEX_BISON environment variable. Please use install cmake target after a successful build.")
    endif()
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /std:c++20")
else()
    if (NOT DEFINED ENV{FLEX_INCLUDE})
        message(FATAL_ERROR "Please set environment variable FLEX_INCLUDE to the directory containing FlexLexer.h")
    endif()
    set(WIN_FLEX_BISON "$ENV{FLEX_INCLUDE}")
endif()

find_package(BISON)
find_package(FLEX)

check_struct_has_member("struct stat.st_mtim" tv_nsec sys/stat.h HAVE_STAT_NSEC LANGUAGE CXX)

# Build

#set_property(GLOBAL PROPERTY JOB_POOLS one_job=1)

if (DEBUG_AND_RELEASE_AND_COVERAGE)
    if (CMAKE_GENERATOR MATCHES "^Visual Studio ")
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

configure_file(include/verilated_config.h.in include/verilated_config.h @ONLY)

configure_package_config_file(verilator-config.cmake.in verilator-config.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_PREFIX}
)

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/verilator-config.cmake DESTINATION ${CMAKE_INSTALL_PREFIX})

configure_package_config_file(verilator-config-version.cmake.in verilator-config-version.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_PREFIX}
)

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/verilator-config-version.cmake DESTINATION ${CMAKE_INSTALL_PREFIX})

foreach (program
    verilator_gantt
    verilator_ccache_report
    verilator_difftree
    verilator_profcfunc
)
    install(PROGRAMS bin/${program} TYPE BIN)
endforeach()

install(DIRECTORY examples TYPE DATA FILES_MATCHING
    PATTERN "examples/*/*.[chv]*"
    PATTERN "examples/*/Makefile*"
    PATTERN "examples/*/CMakeLists.txt"
)

install(DIRECTORY include TYPE DATA FILES_MATCHING
    PATTERN "include/verilated_config.h"
    PATTERN "include/verilated.mk"
    PATTERN "include/*.[chv]"
    PATTERN "include/*.cpp"
    PATTERN "include/gtkwave/*.[chv]*"
    PATTERN "include/vltstd/*.[chv]*"
)
