.. Copyright 2003-2024 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Deprecations
============

The following deprecated items are scheduled for future removal:

C++11 compiler support
  Verilator currently requires a C++20 or newer compiler for timing, and a
  C++14 or newer compiler for both compiling Verilator and compiling
  Verilated models with --no-timing.

  Verilator will require C++20 or newer compilers for both compiling
  Verilator and compiling all Verilated models no sooner than January 2025.
