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

# Each process awaits the edge of its own bit, so verilation must scale linearly with their number.
SIZE_RATIO = 4
SIZE_SMALL = 100
SIZE_LARGE = SIZE_SMALL * SIZE_RATIO
RATIO_MIN = 3
RATIO_MAX = 6  # Linear scaling gives 4x, quadratic gives 16x


def verilation(size, **kwargs):
    test.compile(timing_loop=True,
                 verilator_flags2=[
                     "--timing", "--stats", "--debug", "--debugi 0", "--no-debug-check",
                     "-GSize=" + str(size)
                 ],
                 **kwargs)
    return test.op_count_read(test.stats)


small = verilation(SIZE_SMALL)
test.execute()
large = verilation(SIZE_LARGE, verilator_make_gmake=False)

test.op_count_ok(small, large, RATIO_MIN, RATIO_MAX, r'.*')

test.passes()
