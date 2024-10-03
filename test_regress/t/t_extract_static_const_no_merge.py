#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_extract_static_const.v"
test.golden_filename = "t/t_extract_static_const.out"

test.compile(verilator_flags2=["--stats", "--fno-merge-const-pool"])

test.execute(expect_filename=test.golden_filename)

if test.vlt_all:
    test.file_grep(test.stats, r'Optimizations, Prelim extracted value to ConstPool\s+(\d+)', 8)
    test.file_grep(test.stats, r'ConstPool, Constants emitted\s+(\d+)', 2)

test.passes()
