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
test.top_filename = 't/t_flag_main.v'

for option in ['flatten', 'total']:
    for value in [-1, 101]:
        test.lint(verilator_flags2=[f'--inline-{option}-percent',
                                    str(value)],
                  fails=True,
                  expect_filename=f't/t_inline_percent_bad_{option}_{value}.out')

test.passes()
