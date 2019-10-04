######################################################################
#
# DESCRIPTION: Verilator Python Example: CMakeLists.txt
#
# This is an example cmake script to build a verilog to Python project
# using CMake, Verilator and pybind11.
#
# Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
######################################################################

cmake_minimum_required(VERSION 3.8)
project(cmake_python_example)

find_package(verilator HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
if (NOT verilator_FOUND)
  message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

verilator_add_python_module(Vtop MAIN DOC "An example Verilated Python module")
verilate(Vtop PREFIX Vtop THREADS 4 PYTHON SOURCES top.v)

# A Python module can contain multiple Verilated designs
verilator_add_python_module(example2 MAIN DOC "An example Python module3" EXCLUDE_FROM_ALL)
verilate(example2 PREFIX Vtop THREADS 4 PYTHON SOURCES top.v)
verilate(example2 PREFIX Vtop2 THREADS 4 PYTHON SOURCES top.v)
