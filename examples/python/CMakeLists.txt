cmake_minimum_required(VERSION 3.8)

#[[
To build:
    cd /path/to/verilator/examples/cmake
    mkdir build
    cd build
    cmake ..
    cmake --build .
To run:
    python test_example.py
Or if you have pytest installed:
    pytest test_example.py
]]

cmake_policy(SET CMP0074 NEW)
project(cmake_example)

find_package(verilator HINTS $ENV{VERILATOR_ROOT})
if (NOT verilator_FOUND)
    message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

find_package(pybind11)
if (NOT pybind11_FOUND)
    if (EXISTS ${CMAKE_CURRENT_LIST_DIR}/pybind11)
        add_subdirectory(${CMAKE_CURRENT_LIST_DIR}/pybind11)
    else()
        message(FATAL_ERROR "pybind11 not found. Either install it using your system package manager (e.g. conda install pybind11) or download it locally (git clone https://github.com/pybind/pybind11.git).")
    endif()
endif()

pybind11_add_module(example pyexample.cpp)
#Build 2 versions of the verilog with different parameters
verilate(example NAME Vadd1 SOURCES add.v ARGS -GN=1 --python)
verilate(example NAME Vadd2 SOURCES add.v ARGS -GN=2 --python TRACE)
