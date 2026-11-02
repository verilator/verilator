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
test.compile(verilator_flags2=['--exe', test.pli_filename],
             make_top_shell=False,
             make_main=False,
             threads=1)
test.execute(check_finished=True, all_run_flags=['normal'])
for deferred in [[], ['defer']]:
    for mode in ['add', 'replace', 'missing']:
        test.execute(fails=True,
                     check_finished=False,
                     all_run_flags=[mode] + deferred,
                     expect_filename=('t/t_args_reentrant_missing.out'
                                      if mode == 'missing' else test.golden_filename))
test.passes()
