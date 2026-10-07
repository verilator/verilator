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
test.top_filename = 't/t_inline_percent.v'

test.compile(verilator_flags2=[
    '--inline-flatten-percent', '0', '--inline-total-percent', '100', '-O3', '--inline-mult', '1',
    '--stats'
])
test.execute()
test.file_grep(test.stats, r'Optimizations, Inlined instances\s+(\d+)', 5)

test.passes()
