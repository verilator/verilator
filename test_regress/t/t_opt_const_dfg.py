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
test.top_filename = "t/t_opt_const.v"
test.pli_filename = "t/t_opt_const.cpp"

test.compile(verilator_flags2=["-Wno-UNOPTTHREADS", "--stats", test.pli_filename])

test.execute()

if test.vlt:
    test.file_grep(test.stats, r'Optimizations, Const bit op reduction\s+(\d+)', 38)
    test.file_grep(test.stats, r'SplitVar, packed variables split automatically\s+(\d+)', 1)

test.passes()
