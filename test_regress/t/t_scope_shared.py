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

for count in [7, 127]:
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 verilator_flags2=['--stats', f'-GCOUNT={count}'])
    stats = f'{test.stats}.{count}'
    test.file_sed(test.stats, stats, lambda contents: contents)
    # The wrapper adds scopes for t, $unit, and the constant pool.
    test.file_grep(stats, r'LinkDot, Scope visits\s+(\d+)', 3 * count + 3)

test.passes()
