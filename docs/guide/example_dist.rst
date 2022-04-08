.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Examples in the Distribution:

Examples in the Distribution
============================

See the ``examples/`` directory that is part of the distribution, and
is installed (in a OS-specific place, often in e.g.
``/usr/local/share/verilator/examples``).  These examples include:

examples/make_hello_c
   Example GNU-make simple Verilog->C++ conversion
examples/make_hello_sc
   Example GNU-make simple Verilog->SystemC conversion
examples/make_tracing_c
   Example GNU-make Verilog->C++ with tracing
examples/make_tracing_sc
   Example GNU-make Verilog->SystemC with tracing
examples/make_protect_lib
   Example using --protect-lib
examples/cmake_hello_c
   Example building make_hello_c with CMake
examples/cmake_hello_sc
   Example building make_hello_sc with CMake
examples/cmake_tracing_c
   Example building make_tracing_c with CMake
examples/cmake_tracing_sc
   Example building make_tracing_sc with CMake
examples/cmake_protect_lib
   Example building make_protect_lib with CMake

To run an example copy the example to a new directory and run it.

::

      cp -rp {path_to}/examples/make_hello_c make_hello_c
      cd make_hello_c
      make
