.. Copyright 2003-2021 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Deprecations
============

The following deprecated items are scheduled for future removal:

C++11 compiler support
  Verilator currently requires C++11 or newer compilers.  Verilator will
  require C++14 or newer compilers for both compiling Verilator and
  compiling Verilated models no sooner than January 2022.

Configuration File -msg
  The :vlopt:`lint_off` "-msg" option has been replaced with the "-rule"
  option.  "-msg" is planned for removal no sooner than January 2021.

XML locations
  The XML "fl" attribute has been replaced with the "loc" attribute.  "fl"
  is planned for removal no sooner than January 2021.
