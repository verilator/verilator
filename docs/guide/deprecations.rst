.. Copyright 2003-2023 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Deprecations
============

The following deprecated items are scheduled for future removal:

C++11 compiler support
  Verilator currently requires a C++20 or newer compiler for timing, and a
  C++11 or newer compiler for no-timing.

  Verilator will require C++14 or newer compilers for both compiling
  Verilator and compiling Verilated models with --no-timing no sooner than
  January 2023.

  Verilator will require C++20 or newer compilers for both compiling
  Verilator and compiling all Verilated models no sooner than January 2025.

32-bit compiler support
  Verilator currently regresses both 64-bit and 32-bit pointer modes (GCC's
  `-m64` and `-m32`).  Support for 32-bit `-m32` mode will be deprecated no
  sooner than January 2024.
