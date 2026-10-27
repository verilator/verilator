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
test.top_filename = 't/t_unroll_bit_copy.v'
test.sim_time = 3000

# Exercise the LogAnd form of bounds guards as well as the default Cond form.
test.compile(verilator_flags2=['--stats', '--unroll-count', '8', '--x-assign', '0'])
test.execute()
test.file_grep(test.stats,
               r'Optimizations, Loop unrolling, Lowered bit-copy to part-select\s+(\d+)', 74)
test.passes()
