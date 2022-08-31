.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

*****
Files
*****

.. _Files in the Distribution:

Files in the Git Tree
=====================

The following is a summary of the files in the Git Tree (distribution) of
Verilator:

::

   Changes                     => Version history
   README.rst                  => This document
   bin/verilator               => Compiler wrapper invoked to Verilate code
   docs/                       => Additional documentation
   examples/                   => Examples (see manual for descriptions)
   include/                    => Files that should be in your -I compiler path
   include/verilated*.cpp      => Global routines to link into your simulator
   include/verilated*.h        => Global headers
   include/verilated.mk        => Common Makefile
   src/                        => Translator source code
   test_regress                => Internal tests


.. _Files Read/Written:

Files Read/Written
==================

All output files are placed in the output directory specified with the
:vlopt:`--Mdir` option, or "obj_dir" if not specified.

Verilator creates the following files in the output directory:

For --cc/--sc, it creates:

.. list-table::

   * - *{prefix}*\ .cmake
     - CMake include script for compiling (from --make cmake)
   * - *{prefix}*\ .mk
     - Make include file for compiling (from --make gmake)
   * - *{prefix}*\ _classes.mk
     - Make include file with class names (from --make gmake)
   * - *{prefix}*\ _hier.mk
     - Make file for hierarchy blocks (from --make gmake)
   * - *{prefix}*\ _hierMkArgs.f
     - Arguments for hierarchical Verilation (from --make gmake)
   * - *{prefix}*\ _hierCMakeArgs.f
     - Arguments for hierarchical Verilation (from --make cmake)
   * - *{prefix}*\ .h
     - Model header
   * - *{prefix}*\ .cpp
     - Model C++ file
   * - *{prefix}*\ ___024root.h
     - Top level (SystemVerilog $root) internal header file
   * - *{prefix}*\ ___024root.cpp
     - Top level (SystemVerilog $root) internal C++ file
   * - *{prefix}*\ ___024root\ *{__n}*\ .cpp
     - Additional top level internal C++ files
   * - *{prefix}*\ ___024root\ *{__DepSet_hash__n}*\ .cpp
     - Additional top level internal C++ files (hashed to reduce build times)
   * - *{prefix}*\ ___024root__Slow\ *{__n}*\ .cpp
     - Infrequent cold routines
   * - *{prefix}*\ ___024root\ *{__DepSet_hash__n}*\ .cpp
     - Infrequent cold routines (hashed to reduce build times)
   * - *{prefix}*\ ___024root__Trace\ *{__n}*\ .cpp
     - Wave file generation code (from --trace)
   * - *{prefix}*\ ___024root__Trace__Slow\ *{__n}*\ .cpp
     - Wave file generation code (from --trace)
   * - *{prefix}*\ __Dpi.h
     - DPI import and export declarations (from --dpi)
   * - *{prefix}*\ __Dpi.cpp
     - Global DPI export wrappers (from --dpi)
   * - *{prefix}*\ __Dpi_Export\ *{__n}*\ .cpp
     - DPI export wrappers scoped to this particular model (from --dpi)
   * - *{prefix}*\ __Inlines.h
     - Inline support functions
   * - *{prefix}*\ __Syms.h
     - Global symbol table header
   * - *{prefix}*\ __Syms.cpp
     - Global symbol table C++
   * - *{prefix}{each_verilog_module}*\ .h
     - Lower level internal header files
   * - *{prefix}{each_verilog_module}*\ .cpp
     - Lower level internal C++ files
   * - *{prefix}{each_verilog_module}{__n}*\ .cpp
     - Additional lower C++ files
   * - *{prefix}{each_verilog_module}{__DepSet_hash__n}*\ .cpp
     - Additional lower C++ files (hased to reduce build times)

For --hierarchy mode, it creates:

.. list-table::

   * - V\ *{hier_block}*\ /
     - Directory to Verilate each hierarchy block (from --hierarchy)
   * - *{prefix}*\ __hierVer.d
     - Make dependencies of the top module (from --hierarchy)
   * - *{prefix}*\ __hier.dir
     - Directory to store .dot, .vpp, .tree of top module (from --hierarchy)

In certain debug and other modes, it also creates:

.. list-table::

   * - *{prefix}*\ .xml
     - XML tree information (from --xml)
   * - *{prefix}*\ __cdc.txt
     - Clock Domain Crossing checks (from --cdc)
   * - *{prefix}*\ __stats.txt
     - Statistics (from --stats)
   * - *{prefix}*\ __idmap.txt
     - Symbol demangling (from --protect-ids)
   * - *{prefix}*\ __ver.d
     - Make dependencies (from -MMD)
   * - *{prefix}*\ __verFiles.dat
     - Timestamps (from --skip-identical)
   * - *{prefix}{misc}*\ .dot
     - Debugging graph files (from --debug)
   * - *{prefix}{misc}*\ .tree
     - Debugging files (from --debug)
   * - {mod_prefix}_{each_verilog_base_filename}*\ .vpp
     - Pre-processed verilog (from --debug)

After running Make, the C++ compiler may produce the following:

.. list-table::

   * - verilated{misc}*\ .d
     - Intermediate dependencies
   * - verilated{misc}*\ .o
     - Intermediate objects
   * - {mod_prefix}{misc}*\ .d
     - Intermediate dependencies
   * - {mod_prefix}{misc}*\ .o
     - Intermediate objects
   * - *{prefix}*\
     - Final executable (from --exe)
   * - *{prefix}*\ __ALL.a
     - Library of all Verilated objects
   * - *{prefix}*\ __ALL.cpp
     - Include of all code for single compile
   * - *{prefix}{misc}*\ .d
     - Intermediate dependencies
   * - *{prefix}{misc}*\ .o
     - Intermediate objects

The Verilated executable may produce the following:

.. list-table::

   * - coverage.dat
     - Code coverage output, and default input filename for :command:`verilator_coverage`
   * - gmon.out
     - GCC/clang code profiler output, often fed into :command:`verilator_profcfunc`
   * - profile.vlt
     - --prof-pgo data file for :ref:`Thread PGO`
   * - profile_exec.dat
     - --prof-exec data file for :command:`verilator_gantt`

Verilator_gantt may produce the following:

.. list-table::

   * - profile_exec.vcd
     - Gantt report waveform output
