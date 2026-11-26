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

SIZE_RATIO = 4
SIZE_SMALL = 50
SIZE_LARGE = SIZE_SMALL * SIZE_RATIO
RATIO_MIN = 3
RATIO_MAX = 7  # Linear scaling gives 8x, quadratic gives 32x


def verilation(n):
    test.lint(
        verilator_flags2=[f"-GN={n}", "--stats", "--debug", "--debugi 0", "--no-debug-check"])
    return test.op_count_read(test.stats)


test.op_count_ok(verilation(SIZE_SMALL), verilation(SIZE_LARGE), RATIO_MIN, RATIO_MAX, r'.*')

test.passes()
