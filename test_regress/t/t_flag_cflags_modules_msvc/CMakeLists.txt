######################################################################
#
# DESCRIPTION: CMake script for t_flag_cflags_modules_msvc
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

cmake_minimum_required(VERSION 3.28)
project(t_flag_cflags_modules_msvc CXX)

find_package(verilator REQUIRED)

add_executable(
    t_flag_cflags_modules_msvc ../t_flag_cflags_modules_msvc_main.cpp
)
verilate(
    t_flag_cflags_modules_msvc
    SOURCES ../t_flag_cflags_modules_msvc.v
    VERILATOR_ARGS
        --compiler msvc
        ../t_flag_cflags_modules_msvc.ixx
)
target_compile_features(t_flag_cflags_modules_msvc PRIVATE cxx_std_23)
