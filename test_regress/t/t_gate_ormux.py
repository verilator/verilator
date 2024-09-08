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
test.cycles = (100000000 if test.benchmark else 100)
test.sim_time = test.cycles * 10 + 1000

test.compile(v_flags2=["+define+SIM_CYCLES=" + str(test.cycles)],
             verilator_flags2=["-Wno-UNOPTTHREADS", "--stats", "-fno-dfg"])

if test.vlt:
    test.file_grep(test.stats, r'Optimizations, Const bit op reduction\s+(\d+)', 1058)

test.execute()

test.passes()
