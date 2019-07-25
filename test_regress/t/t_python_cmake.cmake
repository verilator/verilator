# This file ONLY is placed into the Public Domain, for any use,
# without warranty, 2019 by Wilson Snyder.

verilator_add_python_module(example MAIN DOC "An Python module")
verilate(example PREFIX Vadd THREADS 4 TOP_MODULE add PYTHON SOURCES "${CMAKE_CURRENT_LIST_DIR}/t_python_cmake.v" VERILATOR_ARGS -GN=1)

verilator_add_python_module(example2 MAIN DOC "Another Python module")
verilate(example2 PREFIX Vadd TOP_MODULE add PYTHON TRACE SOURCES "${CMAKE_CURRENT_LIST_DIR}/t_python_cmake.v" VERILATOR_ARGS -GN=2)

verilator_add_python_module(example3 MAIN DOC "Yet another Python module")
verilate(example3 PREFIX Vadd TOP_MODULE add PYTHON TRACE_FST SOURCES "${CMAKE_CURRENT_LIST_DIR}/t_python_cmake.v" VERILATOR_ARGS -GN=3)
verilate(example3 PREFIX Vadd2 TOP_MODULE add PYTHON TRACE SOURCES "${CMAKE_CURRENT_LIST_DIR}/t_python_cmake.v" VERILATOR_ARGS -GN=4)
