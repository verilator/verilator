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

# Reuse the same design.  '--x-assign 0' makes the auto-inserted out-of-range guard on a
# non-power-of-two bit-select a plain '(idx <= W-1) && vec[idx]' (AstLogAnd), rather than
# the ternary '(idx <= W-1) ? vec[idx] : <x>' (AstCond) produced under the driver's default
# '--x-assign unique'.  This exercises the matcher's other guard-peel branch.
test.top_filename = "t/t_bit_scan_loops.v"

test.compile(verilator_flags2=['--stats', '--unroll-count', '0', '--x-assign', '0'])

# Same lowering counts as the default run -- only the guard shape differs, not the result.
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered priority-encoder to mostsetbitp1\s+(\d+)',
               8)
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered count-set-bits to countones\s+(\d+)', 1)

test.execute()

test.passes()
