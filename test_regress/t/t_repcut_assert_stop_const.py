#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
from repcut_common import round_robin_partitioner

test.scenarios('vlt_all')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.compile(verilator_flags2=[
    '-frepcut', '--assert', '--timing', '--repcut-partitioner',
    round_robin_partitioner(test)
])
test.execute(fails=True,
             all_run_flags=['+verilator+error+limit+1'],
             expect_filename=test.golden_filename)
test.passes()
