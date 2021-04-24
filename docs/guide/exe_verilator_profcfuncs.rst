.. Copyright 2003-2021 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_profcfuncs
====================

Verilator_profcfunc reads a profile report created by gprof.  The names of
the functions are then transformed, assuming the user used Verilator's
--prof-cfuncs, and a report printed showing the percentage of time, etc, in
each Verilog block.

For an overview of use of verilator_profcfuncs, see :ref:`Profiling`.

verilator_profcfuncs Arguments
------------------------------

.. program:: verilator_profcfuncs

.. option:: <filename>

The :command:`gprof`-generated filename to read data from. Typically "gprof.out".

.. option:: --help

Displays a help summary, the program version, and exits.
