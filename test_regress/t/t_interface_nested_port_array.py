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

# Issue #5066: Nested interface ports through interface arrays
# (e.g., l2.l1[0] where l1 is an interface array inside interface l2).
# V3Param internal errors have been fixed, but V3LinkDot interface
# connection resolution for array element selections is not yet implemented.
# This test documents the current behavior and should be updated when
# full support is added.
test.lint(fails=True, expect_filename=test.golden_filename)

test.passes()
