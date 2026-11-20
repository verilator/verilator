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

# Keep shared copies and the partial-driver chain through coalescing to measure removal.
# N copies, N chain variables and s/chain_s/opposite/zero give 2*N + 4 removals.
SIZE_RATIO = 4
SIZE_SMALL = 100
SIZE_LARGE = SIZE_SMALL * SIZE_RATIO
MIN_RATIO = 3
MAX_RATIO = 6


def verilation(n):
    test.compile(verilator_flags2=[
        "--stats", "--debug", "--debugi 0", "--no-debug-check", "-fno-coalesce", f"-GN={n}"
    ],
                 make_main=False,
                 verilator_make_gmake=False)
    if n == SIZE_SMALL:
        test.file_grep(test.stats, r'Optimizations, DFG, Peephole, remove var\s+(\d+)', 2 * n + 4)
    return test.op_count_read(test.stats)


test.op_count_ok(verilation(SIZE_SMALL), verilation(SIZE_LARGE), MIN_RATIO, MAX_RATIO,
                 r'dfg-peephole$')

test.passes()
