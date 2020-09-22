######################################################################
#
# DESCRIPTION: CMake script for t_hier_block_cmake
#
# Copyright 2003-2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

cmake_minimum_required (VERSION 3.8)
project (t_hier_block_cmake)

find_package(verilator REQUIRED)

add_executable(t_hier_block_cmake  main.cpp ../t_hier_block.cpp)

if(TEST_THREADS)
    set(VERILATOR_OPTIONS "${VERILATOR_OPTIONS}" --threads ${TEST_THREADS})
endif()
set(VERILATOR_OPTIONS "${VERILATOR_OPTIONS}" --hierarchical --stats --CFLAGS "-pipe -DCPP_MACRO=cplusplus")

verilate(t_hier_block_cmake VERILATOR_ARGS ${VERILATOR_OPTIONS} SOURCES
    ../t_hier_block.v )

