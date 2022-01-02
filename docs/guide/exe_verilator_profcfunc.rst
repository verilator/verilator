.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_profcfunc
===================

Verilator_profcfunc reads a profile report created by gprof.  The names of
the functions are then transformed, assuming the user used Verilator's
--prof-cfuncs, and a report printed showing the percentage of time, etc, in
each Verilog block.

Due to rounding errors in gprof reports, the input report's percentages may
not total to 100%.  In the verilator_profcfunc report this will get
reported as a rounding error.

For an overview of use of verilator_profcfunc, see :ref:`Profiling`.

verilator_profcfunc Arguments
-----------------------------

.. program:: verilator_profcfunc

.. option:: <filename>

The :command:`gprof`-generated filename to read data from. Typically "gprof.out".

.. option:: --help

Displays a help summary, the program version, and exits.
