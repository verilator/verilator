.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Deprecations
============

The following deprecated items are scheduled for future removal:

C++11 compiler support
  Verilator currently requires C++11 or newer compilers.  Verilator will
  require C++14 or newer compilers for both compiling Verilator and
  compiling Verilated models no sooner than January 2023.

Verilated_heavy.h
  The legacy "verilated_heavy.h" include was replaced with just including
  "verilated.h". Verilated_heavy.h is planned for removal no sooner than
  July 2022.

Configuration File -msg
  The :vlopt:`lint_off` "-msg" option has been replaced with the "-rule"
  option.  "-msg" is planned for removal no sooner than January 2021.

XML locations
  The XML "fl" attribute has been replaced with the "loc" attribute.  "fl"
  is planned for removal no sooner than January 2021.

Option `--cdc`
  The experimental `--cdc` option is believed to be generally unused and is
  planned for removeal no sooner than January 2023.
