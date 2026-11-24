#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt')

SIZE_RATIO = 4
SIZE_SMALL = 48
SIZE_LARGE = SIZE_SMALL * SIZE_RATIO
RATIO_MIN = 3
RATIO_MAX = 12  # Linear scaling gives 4x, quadratic gives 16x
MAX_MB = 500  # Peak memory limit at the small size (about 50 MB when fine)


def verilation(size):
    test.compile(verilator_flags2=[
        "--stats", "--debug", "--debugi 0", "--no-debug-check", "-GArraySize=" + str(size)
    ],
                 make_main=False,
                 verilator_make_gmake=False)
    return test.op_count_read(test.stats)


small = verilation(SIZE_SMALL)

stats = test.file_contents(test.stats)
peak = re.search(r'Peak Memory Usage \(MB\)\s+(\S+)', stats)
if not peak:
    test.error("Peak memory not found in " + test.stats)
small_mb = float(peak.group(1))
if small_mb > MAX_MB:
    test.error(f"Peak memory with {SIZE_SMALL} forced array elements was {small_mb:.0f} MB " +
               f"(over {MAX_MB} MB)")

large = verilation(SIZE_LARGE)

test.op_count_ok(small, large, RATIO_MIN, RATIO_MAX, r'.*')

test.passes()
