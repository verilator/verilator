#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(verilator_flags2=["--stats", "--unroll-count", "1"])

test.execute()

test.file_grep(test.stats, r'NBA, variables using ShadowVar scheme\s+(\d+)', 1)
test.file_grep(test.stats, r'NBA, variables using ShadowVarMasked scheme\s+(\d+)', 2)
test.file_grep(test.stats, r'NBA, variables using FlagUnique scheme\s+(\d+)', 1)
test.file_grep(test.stats, r'Optimizations, Unrolled Loops\s+(\d+)', 0)
test.file_grep_not(test.stats, r'Warnings, Suppressed BLKANDNBLK')

test.passes()
