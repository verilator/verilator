######################################################################
#
# DESCRIPTION: CMake script for t_flag_cflags_modules_cmake
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

cmake_minimum_required(VERSION 3.28)
project(t_flag_cflags_modules_cmake CXX)

find_package(verilator REQUIRED)

add_executable(
    t_flag_cflags_modules_cmake ../t_flag_cflags_modules_build_main.cpp
)
verilate(
    t_flag_cflags_modules_cmake
    SOURCES ../t_flag_cflags_modules_build.v
    VERILATOR_ARGS
        -CFLAGS -std=c++23
        -CFLAGS -fmodules
        ../t_flag_cflags_modules_build.cppm
)
target_compile_features(t_flag_cflags_modules_cmake PRIVATE cxx_std_23)
