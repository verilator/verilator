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
test.top_filename = 't/t_unroll_nested.v'
test.golden_filename = 't/t_unroll_nested.out'

test.compile(v_flags2=['+define+TEST_FULL', '--stats'])

test.execute(expect_filename=test.golden_filename)

test.file_grep(test.stats, r'Optimizations, Unrolled Iterations\s+(\d+)', 11)
test.file_grep(test.stats, r'Optimizations, Unrolled Loops\s+(\d+)', 4)

test.passes()
