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
test.top_filename = "t/t_reuse.v"

test.compile(verilator_flags2=["--stats", "--trace", "-fno-reuse"])

if test.vlt:
    test.file_grep_not(test.stats, r'Optimizations, Reuse removed temps \s+(\d+)')
    test.file_grep_not(test.stats, r'Optimizations, Reuse total wide temps \s+(\d+)')
elif test.vltmt:
    test.file_grep_not(test.stats, r'Optimizations, Reuse removed temps \s+(\d+)')
    test.file_grep_not(test.stats, r'Optimizations, Reuse total wide temps \s+(\d+)')

test.execute()
test.passes()
