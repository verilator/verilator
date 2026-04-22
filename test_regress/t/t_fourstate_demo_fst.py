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
test.twostate_capable = False

test.top_filename = "t/t_fourstate_demo.v"

test.compile(verilator_flags2=['--binary', '--fourstate', '--trace-fst', '-Wno-FUTURE'])

test.execute(expect_filename='t/t_fourstate_demo.out')

test.trace_identical(test.trace_filename, test.golden_filename)

test.passes()
