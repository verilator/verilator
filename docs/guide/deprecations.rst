.. Copyright 2003-2025 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Deprecations
============

The following deprecated items are scheduled for future removal:

C++14 compiler support
  Verilator currently requires a C++20 or newer compiler for timing, and a
  C++14 or newer compiler for both compiling Verilator and compiling
  Verilated models with --no-timing.

  Verilator will require C++20 or newer compilers for both compiling
  Verilator and compiling all Verilated models no sooner than May 2025.
  (Likely to be removed shortly after GitHub removes Ubuntu 20.04
  continuous-integration action runners, which are used to test the older
  C++ standard).

XML output
  Verilator currently supports XML parser output (enabled with `--xml-only`).
  Support for `--xml-*` options will be deprecated no sooner than January 2026.

--make cmake
  The `--make cmake` options is deprecated and will be removed no sooner than
  January 2026. Use `--make json` instead. Note that the CMake integration
  shipping with Verilator (verilator-config.mk) already uses `--make json` so
  no changes are necessary if using that.
