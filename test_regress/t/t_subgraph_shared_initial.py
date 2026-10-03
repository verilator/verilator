#!/usr/bin/env python3
# DESCRIPTION: Verilator: Shared subgraph logic preserves per-instance initial values
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.compile(make_main=False,
             verilator_flags2=["--subgraph-schedule", "--stats", "--exe", test.pli_filename])
test.execute()

test.file_grep(test.stats, r'Inst, Subgraph shared input captures\s+(\d+)', 2)
test.file_grep(test.stats, r'Scope, Subgraph shared procedures\s+(\d+)', 2)
test.file_grep(test.stats, r'Scope, Subgraph receiver VarScopes\s+(\d+)', 5)
test.file_grep(test.stats, r'Scheduling, Subgraph receiver actives\s+(\d+)', 1)
test.file_grep(test.stats, r'Scheduling, Subgraph receiver late VarScopes\s+(\d+)', 1)
test.file_grep(test.stats, r'Scheduling, Subgraph shared Order skips\s+(\d+)', 2)
implementation = test.obj_dir + "/" + test.vm_prefix + "_sg_shared_initial__0.cpp"
test.file_grep_count(implementation, r'vlSelfRef\.__Vdly__q = vlSelfRef\.__VsubgraphInput__2;', 1)
root_implementation = test.obj_dir + "/" + test.vm_prefix + "___024root__0.cpp"
test.file_grep_count(root_implementation,
                     r'_eval_body__nba_subgraph_pre_0\(\(&vlSymsp->TOP__t__DOT__i_[ab]\)\);', 2)
test.file_grep_not(implementation, r'vlSymsp->TOP__t__DOT__i_[ab]')

test.passes()
