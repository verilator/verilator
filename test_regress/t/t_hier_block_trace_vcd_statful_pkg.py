#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(30)
test.scenarios('vlt_all')
test.top_filename = "t/t_hier_block.v"

test.compile(verilator_flags2=[
    't/t_hier_block.cpp', '--Wno-TIMESCALEMOD', '--trace-vcd', '--trace-underscore',
    "--trace-max-width", "0", "--trace-max-array", "0", "--trace-structs", "--hierarchical",
    "+define+STATEFUL_PKG"
])

test.execute()

test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
