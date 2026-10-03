#!/usr/bin/env python3
# DESCRIPTION: Verilator: Shared subgraph logic scales across receivers
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.compile(verilator_flags2=["--subgraph-schedule", "--stats"])
test.execute()

test.file_grep(test.stats, r'Inst, Subgraph shared input captures\s+(\d+)', 32)
test.file_grep(test.stats, r'Scope, Subgraph shared procedures\s+(\d+)', 62)
test.file_grep(test.stats, r'Scheduling, Subgraph early groups\s+(\d+)', 32)
test.file_grep(test.stats, r'Scheduling, Subgraph early fallbacks\s+(\d+)', 0)
test.file_grep(test.stats, r'Scheduling, Subgraph early clocked actives\s+(\d+)', 2)
test.file_grep(test.stats, r'Scheduling, Subgraph NBA internal actives\s+(\d+)', 2)
test.file_grep(test.stats, r'Scheduling, Subgraph receiver actives\s+(\d+)', 31)
test.file_grep(test.stats, r'Scheduling, Subgraph shared Order skips\s+(\d+)', 62)
child_implementation = test.obj_dir + "/" + test.vm_prefix + "_sg_shared_scale__0.cpp"
root_implementation = test.obj_dir + "/" + test.vm_prefix + "___024root__0.cpp"
test.file_grep_not(child_implementation, r'^void \w+_sg_shared_scale___(?:ico|nba)_sequent__TOP')
test.file_grep_count(root_implementation,
                     r'_eval_body__nba_subgraph_pre_0\(\(&vlSymsp->TOP__t__DOT__g__BRA__', 32)

test.passes()
