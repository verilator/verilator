#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.sim_time = 100000

test.scenarios('simulator')

test.compile(verilator_flags2=["--stats"])

if test.vlt or test.vltmt:
    test.file_grep(test.stats, r"Scheduling, 'act' extra triggers\s+(\d+)", 1)
    test.file_grep(test.stats, r"Scheduling, 'act' pre triggers\s+(\d+)", 1)
    test.file_grep(test.stats, r"Scheduling, 'act' sense triggers\s+(\d+)", 228)

test.execute()

test.passes()
