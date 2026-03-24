#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 by Wilson Snyder.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(
    make_main=False,
    verilator_flags2=[
        '--cc',
        '--exe',
        '--trace-vcd',
        '--trace-structs',
        't/t_trace_dumpvars_cpptop_hier_struct2.cpp',
    ])

test.execute()

test.passes()
