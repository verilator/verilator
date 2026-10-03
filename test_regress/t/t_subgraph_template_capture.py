#!/usr/bin/env python3
# DESCRIPTION: Verilator: Shared subgraph input capture and old output ordering
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt')
test.compile(verilator_flags2=[
    "--subgraph-schedule", "--stats", "--dumpi-graph", "6", "--dumpi-tree-json", "9"
])
test.execute()

test.file_grep(test.stats, r'Inst, Subgraph shared input captures\s+(\d+)', 2)
test.file_grep(test.stats, r'Scope, Subgraph shared procedures\s+(\d+)', 2)
test.file_grep(test.stats, r'Scheduling, Subgraph receiver actives\s+(\d+)', 1)
test.file_grep(test.stats, r'Scheduling, Subgraph shareable CFuncs\s+(\d+)', 5)
test.file_grep(test.stats, r'Scheduling, Subgraph shared Order skips\s+(\d+)', 2)
implementation = test.obj_dir + "/" + test.vm_prefix + "_sg_template_capture__0.cpp"
test.file_grep_count(implementation, r'vlSelfRef\.__Vdly__q = vlSelfRef\.__VsubgraphInput__2;', 1)
root_implementation = test.obj_dir + "/" + test.vm_prefix + "___024root__0.cpp"
test.file_grep_count(root_implementation,
                     r'_eval_body__nba_subgraph_pre_0\(\(&vlSymsp->TOP__t__DOT__i_[ab]\)\);', 2)
test.file_grep_not(implementation, r'vlSelfRef\.q = 0x2aU;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".tree.json", r'"subgraphShareable":true')

graph = test.glob_one(test.obj_dir + "/*nba_orderg_pre.dot")
acyclic = test.glob_one(test.obj_dir + "/*nba_orderg_acyc.dot")
with open(graph, encoding='utf8') as fh:
    contents = fh.read()
with open(acyclic, encoding='utf8') as fh:
    acyclic_contents = fh.read()
nodes = dict(re.findall(r'^\s*n(\d+)\s+\[.*label="(.*?)", color=', contents, re.MULTILINE))
edges = set(re.findall(r'^\s*n(\d+) -> n(\d+)', contents, re.MULTILINE))
acyclic_edges = set(re.findall(r'^\s*n(\d+) -> n(\d+)', acyclic_contents, re.MULTILINE))
captures = [
    node for node, label in nodes.items() if 'i_a->__VsubgraphInput__2' in label
    and 'PORD' not in label and 'PRE' not in label and 'POST' not in label
]
old_b = [
    node for node, label in nodes.items()
    if 'i_b->__VsubgraphPublished__0' in label and 'POST' in label
]
if len(captures) != 1 or len(old_b) != 1:
    test.error("Missing capture or old published output in parent Order graph")
else:
    writers = [
        source for source, target in edges
        if target == captures[0] and 'ALWAYS' in nodes.get(source, '')
    ]
    consumers = [
        target for source, target in edges
        if source == captures[0] and 'ACTIVE' in nodes.get(target, '')
    ]
    if len(writers) != 1 or len(consumers) != 1 \
            or (writers[0], old_b[0]) not in edges & acyclic_edges \
            or (captures[0], consumers[0]) not in edges & acyclic_edges:
        test.error("Old child output was not consumed before the next capture")

test.passes()
