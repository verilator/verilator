######################################################################
#
# DESCRIPTION: Verilator CMake Example: Small CMakeLists.txt
#
# This is an example cmake script to build a verilog to systemc project
# using cmake and verilator.
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2020 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0
#
######################################################################

# This example builds the tracing_c example using CMake
# To use it, run the following:

# cd /path/to/verilator/examples/cmake_c
# rm -rf build && mkdir build && cd build
# cmake ..
# cmake --build .

cmake_minimum_required(VERSION 3.8)
project(cmake_protect_lib)

find_package(verilator HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
if (NOT verilator_FOUND)
  message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

# Create the main executable target
add_executable(example ../make_protect_lib/sim_main.cpp)

# Create a secret library
add_library(verilated_secret STATIC) # or SHARED for a shared library
target_link_libraries(example PRIVATE verilated_secret)
# To create both libraries on CMake >= 3.12 replace the above 2 lines with the following:
# add_library(verilated_secret OBJECT)
# set_property(TARGET verilated_secret PROPERTY POSITION_INDEPENDENT_CODE 1)
# add_library(verilated_secret_static STATIC  $<TARGET_OBJECTS:verilated_secret>)
# set_target_properties(verilated_secret_static PROPERTIES OUTPUT_NAME verilated_secret)
# add_library(verilated_secret_shared SHARED  $<TARGET_OBJECTS:verilated_secret>)
# set_target_properties(verilated_secret_shared PROPERTIES OUTPUT_NAME verilated_secret)
# target_link_libraries(example PRIVATE verilated_secret_static)

# Setup random seed
verilator_generate_key(KEY_INIT)
set(PROTECT_KEY ${KEY_INIT} CACHE STRING "Random seed for protection")

# Add the Verilated modules to the targets
verilate(verilated_secret
  VERILATOR_ARGS --protect-lib verilated_secret
                 --protect-key ${PROTECT_KEY}
  DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/verilated_secret
  SOURCES ../make_protect_lib/secret_impl.v)

# Include location of verilated_secret.sv wrapper
verilate(example
  VERILATOR_ARGS "-I${CMAKE_CURRENT_BINARY_DIR}/verilated_secret"
  SOURCES ../make_protect_lib/top.v)
