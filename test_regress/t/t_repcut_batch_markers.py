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

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = "t/t_inst_first.v"
test.compile(threads=2,
             verilator_flags2=[
                 '-frepcut', '--stats', '--dumpi-tree', '3', '--dumpi-tree-json', '3',
                 '--no-json-ids', '--repcut-partitioner',
                 round_robin_partitioner(test)
             ])
test.execute()
test.file_grep(test.stats, r'RepCut native batch, domains\s+(\d+)', 2)
test.file_grep(test.glob_one(test.obj_dir + '/*_sched.tree'), r'\[REPCUTBATCHROOT\]')
test.file_grep(test.glob_one(test.obj_dir + '/*_sched.tree.json'), r'"repcutBatchRoot":\s*true')
test.passes()
