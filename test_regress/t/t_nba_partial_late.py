#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

# Exercise ascending packed ranges and a slice extending past the upper bound.
test.compile(verilator_flags2=['--stats', '-Wno-ASCRANGE', '-Wno-SELRANGE'])
if test.vlt_all:
    test.file_grep(test.stats, r'Optimizations, Lifetime NBA copy words removed\s+(\d+)', 512)
test.execute()
test.passes()
