..
   SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
   SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Deprecations
============

The following deprecated items are scheduled for future removal:

C++14 compiler support
   Verilator currently requires a C++20 or newer compiler for timing, and a
   C++14 or newer compiler for both compiling Verilator and compiling
   Verilated models with --no-timing.

   Verilator will require C++20 or newer compilers for both compiling
   Verilator and compiling all Verilated models no sooner than May 2025.
   (Although this date has expired, this change is currently on hold until
   the Ubuntu LTS versions of GCC and clang use C++20 by default, estimated
   May 2028.)

tcmalloc support
   Verilator currently supports the default malloc, tcmalloc, or jemalloc.
   As jemalloc has better performance, support for tcmalloc may be removed
   no sooner than January 2027.

Pragma :option:`/*verilator&32;fsm_reset_arc*/`
   Verilator currently supports :option:`/*verilator&32;fsm_reset_arc*/`
   which aliases :option:`/*verilator&32;fsm_state*/`. This alias may be
   removed no sooner than February 2027.
