#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--stats'])

# Exactly 4 loops must lower to $mostsetbitp1: the 3 canonical I/Q/W leading-one
# loops plus the unsigned-index one.  The 6 negative loops (incl. W != width) must
# be left alone -- a wrong lowering would push the count above 4.
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered priority-encoder to mostsetbitp1\s+(\d+)',
               4)
# And the one count-ones loop must lower to $countones.
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered count-set-bits to countones\s+(\d+)',
               1)

test.execute()

test.passes()
