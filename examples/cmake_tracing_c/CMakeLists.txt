######################################################################
#
# DESCRIPTION: Verilator CMake Example: Small CMakeLists.txt with tracing
#
# This is an example cmake script to build a verilog to systemc project
# using cmake and verilator.
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2020 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0
#
######################################################################

# This example builds the make_tracing_c example using CMake
# To use it, run the following:

# cd /path/to/verilator/examples/cmake_tracing_c
# rm -rf build && mkdir build && cd build
# cmake ..
# cmake --build .

cmake_minimum_required(VERSION 3.12)
cmake_policy(SET CMP0074 NEW)
project(cmake_tracing_c)

find_package(verilator HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
if(NOT verilator_FOUND)
    message(
        FATAL_ERROR
        "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable"
    )
endif()

# Create a new executable target that will contain all your sources
add_executable(example ../make_tracing_c/sim_main.cpp)
target_compile_features(example PUBLIC cxx_std_14)

# Add the Verilated circuit to the target
verilate(example COVERAGE TRACE_VCD
  INCLUDE_DIRS "../make_tracing_c"
  VERILATOR_ARGS -f ../make_tracing_c/input.vc -x-assign fast
  SOURCES ../make_tracing_c/top.v
)
