#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

# A clocking block 'output' drives the signal it names. Against a continuous
# assignment or a second clocking block that is an unambiguous driver conflict
# (MULTIDRIVEN, on by default); against a plain always block it is a common
# testbench idiom, so it is only reported under MULTIDRIVENPROC, enabled here
# explicitly. Signals driven by a single clocking block, only read by one, named
# by two clockvars of one clocking block, or carrying just a declaration
# initializer must not warn at all.
test.lint(fails=True,
          verilator_flags2=['-Wwarn-MULTIDRIVENPROC'],
          expect_filename=test.golden_filename)

test.passes()
