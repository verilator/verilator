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
test.top_filename = "t/t_wide_temp_opt.v"

test.compile(verilator_flags2=["--stats", "--trace", "-fno-expand"])

if test.vlt:
    test.file_grep(test.stats, r'Optimizations, ReuseWideTemps removed temps \s+(\d+)', 20)
    test.file_grep(test.stats, r'Optimizations, ReuseWideTemps total wide temps \s+(\d+)', 25)
elif test.vltmt:
    test.file_grep(test.stats, r'Optimizations, ReuseWideTemps removed temps \s+(\d+)', 12)
    test.file_grep(test.stats, r'Optimizations, ReuseWideTemps total wide temps \s+(\d+)', 25)

test.execute()
test.passes()
