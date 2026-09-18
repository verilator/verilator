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
test.compile(verilator_flags2=['--coverage'], threads=(2 if test.vltmt else 1))
for kind, value in [('scalar', 5), ('array', 1), ('wildcard', 6)]:
    test.execute(fails=True,
                 check_finished=False,
                 all_run_flags=[f'+value={value}'],
                 logfile=f'{test.obj_dir}/vlt_{kind}.log',
                 expect_filename=test.golden_filename.replace('.out', f'.{kind}.out'))
test.passes()
