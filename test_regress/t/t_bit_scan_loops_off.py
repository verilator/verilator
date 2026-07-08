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

# Reuse the same design; only the optimization switch differs.
test.top_filename = "t/t_bit_scan_loops.v"

test.compile(verilator_flags2=['--stats', '--unroll-count', '0', '-fno-bit-scan-loops'])

# With the optimization disabled, nothing lowers.
test.file_grep(test.stats, r'Lowered priority-encoder to mostsetbitp1\s+([0-9])', 0)

test.execute()

test.passes()
