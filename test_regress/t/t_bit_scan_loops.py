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

# --unroll-count 0 so the loops are recognized without relying on unrolling.
test.compile(verilator_flags2=['--stats', '--unroll-count', '0'])

# The leading-one positives lower to $mostsetbitp1, the count-ones positive to
# $countones; the negatives are left as loops (a wrong lowering would raise a count).
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered priority-encoder to mostsetbitp1\s+(\d+)',
               8)
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered count-set-bits to countones\s+(\d+)', 1)

test.execute()

test.passes()
