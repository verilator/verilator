#!/usr/bin/env python3
# DESCRIPTION: Verilator: Finish propagation in intra-assignment expressions without lifting
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = 't/t_finish_intra_assign.v'

modes = ('delay', 'lhs_nba', 'lhs_blocking', 'lhs_event', 'nba_complete')

test.compile(verilator_flags2=['--binary', '--no-sched-zero-delay', '-fno-lift-expr'])
for mode in modes:
    test.execute(all_run_flags=[f'+MODE={mode}'], logfile=test.obj_dir + f'/sim_{mode}.log')

test.passes()
