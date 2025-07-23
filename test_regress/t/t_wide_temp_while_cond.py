#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(
    verilator_flags2=["--exe", "--main", "--timing", "--stats", "t/t_wide_temp_while_cond.cpp"])

if test.vlt or test.vltmt:
    test.file_grep(test.stats, r'Optimizations, Prelim temporary variables created\s+(\d+)', 3)

test.execute()

test.passes()
