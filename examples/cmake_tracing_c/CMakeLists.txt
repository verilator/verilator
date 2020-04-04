######################################################################
#
# DESCRIPTION: Verilator CMake Example: Small CMakeLists.txt with tracing
#
# This is an example cmake script to build a verilog to systemc project
# using cmake and verilator.
#
# Copyright 2003-2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

# This example builds the make_tracing_c example using CMake
# To use it, run the following:

# cd /path/to/verilator/examples/cmake_tracing_c
# rm -rf build && mkdir build && cd build
# cmake ..
# cmake --build .

cmake_minimum_required(VERSION 3.8)
project(cmake_tracing_c)

find_package(verilator HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
if (NOT verilator_FOUND)
  message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

# Create a new executable target that will contain all your sources
add_executable(example ../make_tracing_c/sim_main.cpp)

# Add the Verilated circuit to the target
verilate(example COVERAGE TRACE
  INCLUDE_DIRS "../make_tracing_c"
  VERILATOR_ARGS -f ../make_tracing_c/input.vc -Os -x-assign 0
  SOURCES ../make_tracing_c/top.v)
