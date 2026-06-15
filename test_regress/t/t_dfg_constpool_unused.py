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

test.compile(verilator_flags2=['--binary', '--stats'])

test.file_grep(test.stats, r'Optimizations, Cases table normal\s+(\d+)', 1)
test.file_grep(test.stats, r'Optimizations, DFG, Peephole, remove var\s+(\d+)', 2)
test.file_grep_not(test.stats, r'ConstPool, Constants emitted')  # Removed by V3Dead later

test.passes()
