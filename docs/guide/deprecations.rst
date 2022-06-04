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

Option `--cdc`
  The experimental `--cdc` option is believed to be generally unused and is
  planned for removal no sooner than January 2023.

Option `-O<letter>`
  The debug `-O<letter>` options have been replaced with
  `-fno-<optimization>` debug options to match GCC. The old options are
  planned for removal no sooner than June 2023.

Option `--prof-threads`
  The `--prof-threads` option has been superseded by the `--prof-exec` and
  `--prof-pgo` options and is planned for removal no sooner than April 2023.

Verilated model options `+verilator+prof+threads+*`
  The `+verilator+prof+threads+start`, `+verilator+prof+threads+window` and
  `+verilator+prof+threads+file` options have been superseded by the
  `+verilator+prof+exec+start`, `+verilator+prof+exec+window` and
  `+verilator+prof+exec+file` options respectively and are planned for removal
  no sooner than April 2023.
