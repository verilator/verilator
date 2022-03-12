######################################################################
#
# DESCRIPTION: CMake script for regression tests
#
# This CMake file is meant to be consumed by regression tests.
#
# Copyright 2003-2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

cmake_minimum_required(VERSION 3.8)
set(TEST_REQUIRED_VARS NAME CSOURCES OPT_FAST OPT_GLOBAL
                            VERILATOR_ROOT VERILATOR_ARGS
                            VERILATOR_SOURCES SYSTEMC VERBOSE VERILATION)
foreach(var ${TEST_REQUIRED_VARS})
  if (NOT DEFINED TEST_${var})
    message(FATAL_ERROR "TEST_${var} not defined. This CMakeLists.txt file is meant to be run by driver.pl.")
  endif()
endforeach()

project("${TEST_NAME}")

if(TEST_VERBOSE)
  add_definitions(-DTEST_VERBOSE=1)
endif()

separate_arguments(TEST_VERILATOR_ARGS UNIX_COMMAND "${TEST_VERILATOR_ARGS}")

# filter out empty arguments
list(FILTER TEST_VERILATOR_ARGS EXCLUDE REGEX "$^")

set(TEST_PREFIX ${TEST_NAME})

# If --ARG <val> is present, set OUT = <val>
function(getarg LST ARG OUT)
  list(FIND ${LST} ${ARG} _INDEX)
  if(NOT _INDEX EQUAL -1)
    list(REMOVE_AT ${LST} ${_INDEX})
    list(GET ${LST} ${_INDEX} VAL)
    set(${OUT} ${VAL} PARENT_SCOPE)
  endif()
endfunction()

# Normalise -- to -
string(REGEX REPLACE "(^|;)--" "\\1-"
       TEST_VERILATOR_ARGS_NORM
       "${TEST_VERILATOR_ARGS}")

getarg(TEST_VERILATOR_ARGS_NORM "-prefix" TEST_PREFIX)
getarg(TEST_VERILATOR_ARGS_NORM "-threads" TEST_THREADS)
getarg(TEST_VERILATOR_ARGS_NORM "-trace-threads" TEST_TRACE_THREADS)

# Strip unwanted args with 1 parameter
string(REGEX REPLACE "(^|;)--?(Mdir|make|prefix|threads|trace-threads);[^;]*" ""
       TEST_VERILATOR_ARGS
       "${TEST_VERILATOR_ARGS}")
# Strip unwanted args
string(REGEX REPLACE "(^|;)--?(sc|cc)" ""
       TEST_VERILATOR_ARGS
       "${TEST_VERILATOR_ARGS}")

separate_arguments(TEST_VERILATOR_SOURCES UNIX_COMMAND "${TEST_VERILATOR_SOURCES}")
# filter out empty sources
list(FILTER TEST_VERILATOR_SOURCES EXCLUDE REGEX "$^")

find_package(verilator REQUIRED HINTS ${TEST_VERILATOR_ROOT})

set(verilate_ARGS MAIN)
if(TEST_PREFIX)
  list(APPEND verilate_ARGS PREFIX ${TEST_PREFIX})
endif()
if(TEST_OPT_FAST)
  list(APPEND verilate_ARGS OPT_FAST ${TEST_OPT_FAST})
endif()
if(TEST_OPT_GLOBAL)
  list(APPEND verilate_ARGS OPT_GLOBAL ${TEST_OPT_GLOBAL})
endif()
if(TEST_THREADS)
  list(APPEND verilate_ARGS THREADS ${TEST_THREADS})
endif()
if(TEST_TRACE_THREADS)
  list(APPEND verilate_ARGS TRACE_THREADS ${TEST_TRACE_THREADS})
endif()
if(TEST_SYSTEMC)
  list(APPEND verilate_ARGS SYSTEMC)
endif()

set(TARGET_NAME "V${TEST_NAME}")

add_executable(${TARGET_NAME} ${TEST_CSOURCES})

if(TEST_VERILATION)
  verilate(${TARGET_NAME} ${verilate_ARGS}
           VERILATOR_ARGS ${TEST_VERILATOR_ARGS}
           DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
           SOURCES ${TEST_VERILATOR_SOURCES})
endif()

if(TEST_SYSTEMC)
  verilator_link_systemc("${TARGET_NAME}")
endif()

string(TOUPPER "${TEST_NAME}" TEST_NAME_UC)

target_compile_definitions(${TARGET_NAME} PRIVATE
  "TEST_OBJ_DIR=${CMAKE_CURRENT_BINARY_DIR}"
  "VM_PREFIX=${TEST_PREFIX}"
  "VM_PREFIX_INCLUDE=<${TEST_PREFIX}.h>"
  "${TEST_NAME_UC}"
)
