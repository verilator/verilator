#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(verilator_flags2=["--binary", "--stats"])

test.execute(expect_filename=test.golden_filename)

test.file_grep(test.stats, r'Optimizations, Loop unrolling, Failed - contains fork\s+(\d+)', 0)
test.file_grep(test.stats, r'Optimizations, Loop unrolling, Failed - infinite loop\s+(\d+)', 0)
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Failed - loop test in sub-statement\s+(\d+)', 0)
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Failed - reached --unroll-count\s+(\d+)', 0)
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Failed - reached --unroll-stmts\s+(\d+)', 0)
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Failed - unknown loop condition\s+(\d+)', 0)
test.file_grep(test.stats, r'Optimizations, Loop unrolling, Pragma unroll_disable\s+(\d+)', 0)
test.file_grep(test.stats, r'Optimizations, Loop unrolling, Unrolled loops\s+(\d+)', 6)
test.file_grep(test.stats, r'Optimizations, Loop unrolling, Unrolled iterations\s+(\d+)', 40)

test.passes()
