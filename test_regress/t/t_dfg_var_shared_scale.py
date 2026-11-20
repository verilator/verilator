#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if test.have_dev_gcov:
    test.skip("Too slow with code coverage")
if test.have_dev_asan or test.tsan:
    test.skip("Too slow with sanitizers")

SIZE_RATIO = 4
SIZE_SMALL = 100
SIZE_LARGE = SIZE_SMALL * SIZE_RATIO
MIN_RATIO = 3
MAX_RATIO = 6


def verilation(n, nobs):
    flags = ["--stats", "--debug", "--debugi 0", "--no-debug-check", f"-GN={n}", f"-GNOBS={nobs}"]
    test.compile(verilator_flags2=flags, make_main=False, verilator_make_gmake=False)
    test.file_cache_clear()
    test.file_grep(test.stats, r'Optimizations, DFG, CSE 1st, expressions eliminated\s+(\d+)',
                   2 * n if nobs else 2 * n - 2)
    test.file_grep(test.stats, r'Optimizations, DFG, Peephole, remove var\s+(\d+)',
                   0 if nobs else n)
    return test.op_count_read(test.stats)


# Copies of an expression that has two other uses are kept
test.op_count_ok(verilation(SIZE_SMALL, 2), verilation(SIZE_LARGE, 2), MIN_RATIO, MAX_RATIO,
                 r'dfg-peephole$')
# Copies of an expression that has no other use are removed
test.op_count_ok(verilation(SIZE_SMALL, 0), verilation(SIZE_LARGE, 0), MIN_RATIO, MAX_RATIO,
                 r'dfg-peephole$')

test.passes()
