#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = 't/t_cover_lib.v'

test.compile(verilator_flags2=['--coverage', '--exe', test.pli_filename],
             make_top_shell=False,
             make_main=False,
             threads=(2 if test.vltmt else 1))

# Exercise immediate callbacks and callbacks dispatched after the coverage call returns.
for run_flags in [[], ['+defer']]:
    test.execute(fails=True,
                 check_finished=False,
                 all_run_flags=run_flags,
                 expect_filename=test.golden_filename)

    # Cover both reserved key forms: a single character and a letter followed by a digit.
    for key in ['x', 'x1']:
        test.execute(fails=True,
                     check_finished=False,
                     all_run_flags=run_flags + ['+key=' + key],
                     expect_filename='t/t_cover_error_' + key + '.out')

test.passes()
