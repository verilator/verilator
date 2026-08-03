#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

test.execute()

# The impossible class names both of its constraints in the unsat core
test.file_grep(test.run_log_filename, r'UNSATCONSTR.*x dist \{8.d1 := 1, 8.d2 := 1\}')
test.file_grep(test.run_log_filename, r'UNSATCONSTR.*x == 8.d5')
# The narrowed class solves, so nothing about it is reported
test.file_grep_not(test.run_log_filename, r'UNSATCONSTR.*y dist')
test.file_grep_not(test.run_log_filename, r'UNSATCONSTR.*y == 8.d2')

test.passes()
