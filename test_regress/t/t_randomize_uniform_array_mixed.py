#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import randomize_uniform_common

test.scenarios('simulator')

# (sel, arr[0], arr[1]): sel==1 -> arr[0] > arr[1]; sel==0 -> arr[0] <= arr[1]
SOLUTIONS = [
    '%d %d %d' % ((1 if arr0 > arr1 else 0), arr0, arr1) for arr0 in range(8) for arr1 in range(8)
]

randomize_uniform_common.run(test, SOLUTIONS, r'\d+ \d+ \d+')
