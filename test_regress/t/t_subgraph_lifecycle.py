#!/usr/bin/env python3
# DESCRIPTION: Verilator: Subgraph boundary identities across compiler stages
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(
    verilator_flags2=["--subgraph-schedule", "--stats", "--dump-tree", "--dump-tree-json"])
test.execute()

test.file_grep(test.stats, r'Subgraph boundary, elaborated specializations\s+(\d+)', 2)
test.file_grep(test.stats, r'Subgraph boundary, elaborated ports\s+(\d+)', 8)
test.file_grep(test.stats, r'Subgraph boundary, prepared connections\s+(\d+)', 9)
test.file_grep(test.stats, r'Subgraph boundary, resolved instances\s+(\d+)', 3)
test.file_grep(test.stats, r'Subgraph boundary, scoped publications\s+(\d+)', 3)
test.file_grep(test.stats, r'Subgraph boundary, delayed publications\s+(\d+)', 3)
test.file_grep(test.stats, r'Subgraph boundary, NBA publications\s+(\d+)', 3)
test.file_grep(test.stats, r'Subgraph boundary, connected wrappers\s+(\d+)', 6)
test.file_grep(test.stats, r'Inst, Subgraph shared input captures\s+(\d+)', 2)
test.file_grep(test.stats, r'Scope, Subgraph shared procedures\s+(\d+)', 2)
test.file_grep(test.stats, r'Scheduling, Subgraph receiver actives\s+(\d+)', 1)
test.file_grep(test.stats, r'Scheduling, Subgraph shareable CFuncs\s+(\d+)', 5)
test.file_grep(test.stats, r'Scheduling, Subgraph shared Order skips\s+(\d+)', 2)

metadata = test.obj_dir + "/" + test.vm_prefix + "__subgraph_boundary.txt"
test.file_grep_count(metadata, r'port \d+ width=7 direction=OUTPUT', 2)
test.file_grep_count(metadata, r'port \d+ width=15 direction=OUTPUT', 2)
test.file_grep_count(metadata, r'event POS references=1', 2)
test.file_grep_count(metadata, r'connection port=2 width=7 shape=CONST references=0', 1)
test.file_grep_count(metadata, r'connection port=3 width=7 shape=VARREF references=1', 2)
test.file_grep(metadata, r"instance=t__DOT__i_b expression=7'h2a")

implementation = test.obj_dir + "/" + test.vm_prefix + "_sg_lifecycle__0.cpp"
test.file_grep_count(implementation, r'vlSelfRef\.__Vdly__q = vlSelfRef\.__VsubgraphInput__2;', 1)
test.file_grep_not(implementation, r'vlSelfRef\.q = 0x2aU;')

test.passes()
