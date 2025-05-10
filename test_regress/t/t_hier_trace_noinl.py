#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_hier_trace.v"

test.compile(verilator_flags2=[
    '--trace-vcd', '-j 4', 't/t_hier_trace_sub/t_hier_trace.vlt', '--top-module t',
    '--hierarchical', '--fno-inline', '-F t/t_hier_trace_sub/top.F'
])

test.execute(all_run_flags=['-j 4'])

test.vcd_identical(test.trace_filename, test.golden_filename)

test.passes()
