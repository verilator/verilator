# -*- CMake script -*-
######################################################################
# DESCRIPTION: CMake script to generate a python module for verilated modules
#
# Copyright 2003-2019 by Wilson Snyder. Verilator is free software; you can
# redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Perl Artistic License Version 2.0.
######################################################################

cmake_minimum_required(VERSION 3.8)

if (NOT CMAKE_SCRIPT_MODE_FILE)
  message(FATAL_ERROR "This file is meant to be used in scripting mode")
endif()

if (NOT OUTPUT)
  message(FATAL_ERROR "Missing OUTPUT argument")
endif()

if (NOT NAME)
  message(FATAL_ERROR "Missing NAME argument")
endif()

if (NOT PREFIXES)
  message(FATAL_ERROR "Missing PREFIXES argument")
endif()

set(O "${OUTPUT}")

file(WRITE "${O}" "// Verilated -*- C++ -*-\n")
file(APPEND "${O}" "// DESCR" "IPTION: Generated global Python module\n")
file(APPEND "${O}" "\n")
foreach(PREFIX ${PREFIXES})
  file(APPEND "${O}" "#include \"${PREFIX}_py.h\"\n")
endforeach()
file(APPEND "${O}" "\n")
file(APPEND "${O}" "#include <pybind11/pybind11.h>\n")
file(APPEND "${O}" "\n")
file(APPEND "${O}" "// Declare a pybind11 module\n")
file(APPEND "${O}" "PYBIND11_MODULE(${NAME}, m) {\n")
if (DOCUMENTATION)
  file(APPEND "${O}" "    m.doc() = \"${DOCUMENTATION}\";\n")
  file(APPEND "${O}" "\n")
endif()
file(APPEND "${O}" "    // declare the common parts of Verilator (Verilated class and tracing classes)\n")
file(APPEND "${O}" "    vl_py::declare_globals(m);\n")
file(APPEND "${O}" "\n")
foreach (PREFIX ${PREFIXES})
  file(APPEND "${O}" "    // declare ${PREFIX}\n")
  file(APPEND "${O}" "    vl_py::declare_${PREFIX}(m);\n")
endforeach()
file(APPEND "${O}" "}\n")
