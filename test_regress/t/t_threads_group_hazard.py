#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_threads_group.v"

# Keep the two accesses as separate logic blocks, so one MTask holds several accesses to hazard_q
test.compile(
    verilator_flags2=["-fno-dfg", "-CFLAGS", "-DVL_THREADS_SERIAL_COST=0"],
    threads=2)

test.execute()
test.passes()
