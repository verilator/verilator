#!/usr/bin/env python3
# DESCRIPTION: Verilator: Subgraph NBA capture, evaluate, and publish ordering
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt')
test.pli_filename = "t/t_subgraph_phase.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--cc",
                 "--exe",
                 test.pli_filename,
                 "--subgraph-schedule",
                 "-Wno-fatal",
                 "--stats",
                 "--dumpi-graph 6",
             ])
test.execute()

test.file_grep(test.stats, r'Subgraph boundary, elaborated specializations\s+(\d+)', 6)
test.file_grep(test.stats, r'Subgraph boundary, elaborated ports\s+(\d+)', 24)
test.file_grep(test.stats, r'Subgraph boundary, elaborated NBA assignments\s+(\d+)', 12)
test.file_grep(test.stats, r'Subgraph boundary, elaborated events\s+(\d+)', 7)
test.file_grep(test.stats, r'Subgraph boundary, prepared connections\s+(\d+)', 24)
test.file_grep(test.stats, r'Subgraph boundary, resolved instances\s+(\d+)', 6)
test.file_grep(test.stats, r'Subgraph boundary, scoped publications\s+(\d+)', 6)
test.file_grep(test.stats, r'Subgraph boundary, delayed publications\s+(\d+)', 6)
test.file_grep(test.stats, r'Subgraph boundary, NBA publications\s+(\d+)', 6)
test.file_grep(test.stats, r'Subgraph boundary, NBA shadow pairs\s+(\d+)', 6)
test.file_grep(test.stats, r'Subgraph boundary, connected wrappers\s+(\d+)', 15)

test.file_grep(test.stats, r'Scheduling, Subgraph NBA groups\s+(\d+)', 5)
test.file_grep(test.stats, r'Scheduling, Subgraph NBA internal actives\s+(\d+)', 10)
test.file_grep(test.stats, r'Scheduling, Subgraph early candidates\s+(\d+)', 6)
test.file_grep(test.stats, r'Scheduling, Subgraph early groups\s+(\d+)', 5)
test.file_grep(test.stats, r'Scheduling, Subgraph early fallbacks\s+(\d+)', 1)
test.file_grep(test.stats, r'Scheduling, Subgraph early clocked actives\s+(\d+)', 10)
test.file_grep(test.stats, r'Scheduling, Subgraph captured inputs\s+(\d+)', 13)
test.file_grep(test.stats, r'Inst, Subgraph published outputs\s+(\d+)', 6)
published_headers = test.glob_some(test.obj_dir + "/*sg_phase_direct_ff.h")
if len(published_headers) != 1:
    test.error("Expected one direct FF implementation header")
else:
    test.file_grep(published_headers[0], r'__VsubgraphPublished__0')

sched_graphs = test.glob_some(test.obj_dir + "/*_sched.dot")
if len(sched_graphs) != 6:
    test.error("Expected five child scheduler graphs and one parent graph, got " +
               str(len(sched_graphs)))

boundary_cases = ('i_direct', 'i_serial0', 'i_serial1', 'i_ring_a', 'i_ring_b')
published_targets = {
    'i_direct': 'direct',
    'i_serial0': 'serial0',
    'i_serial1': 'serial1',
    'i_ring_a': 'ring_a',
    'i_ring_b': 'ring_b',
}
parent_sched = []
for filename in sched_graphs:
    with open(filename, 'r', encoding='utf8') as fh:
        contents = fh.read()
    if "__Vdly__parent_q" in contents:
        parent_sched.append(contents)
if len(parent_sched) != 1:
    test.error("Expected one parent scheduler graph, got " + str(len(parent_sched)))
else:
    parent_sched = parent_sched[0]
    partition_nodes = dict(
        re.findall(r'^\s*n(\d+)\s+\[fontsize=8 label="([^"]*)"', parent_sched, re.MULTILINE))
    partition_edges = set(re.findall(r'\bn(\d+) -> n(\d+)', parent_sched))
    clocks = [node for node, label in partition_nodes.items() if label == 'posedge clk']
    if len(clocks) != 1:
        test.error("Expected one parent clock event")
    for instance in boundary_cases:
        boundary = [
            node for node, label in partition_nodes.items()
            if label.startswith(r'SUBGRAPH\n') and label.endswith(instance)
        ]
        if len(boundary) != 1:
            test.error("Expected one parent partition boundary for " + instance)
            continue
        if any(
                label.endswith(instance + '->__Vdly__state') or label.endswith(instance +
                                                                               '->__Vdly__q')
                for label in partition_nodes.values()):
            test.error("Child NBA temporary leaked into parent scheduler: " + instance)
        if len(clocks) == 1 and (clocks[0], boundary[0]) not in partition_edges:
            test.error("Missing parent boundary clock for " + instance)
        published = [
            node for node, label in partition_nodes.items()
            if label.endswith(instance + '->__VsubgraphPublished__0')
        ]
        target = [
            node for node, label in partition_nodes.items()
            if label == 'TOP->' + published_targets[instance]
        ]
        if len(published) != 1 or len(target) != 1:
            test.error("Missing published value or output for " + instance)
            continue
        if (boundary[0], published[0]) not in partition_edges:
            test.error("Missing port-level boundary write for " + instance)
        writers = [source for source, sink in partition_edges if sink == published[0]]
        if writers != boundary:
            test.error("Parent scheduler has another published-value writer: " + instance)
        output_logic = [
            node for node in partition_nodes
            if (published[0], node) in partition_edges and (node, target[0]) in partition_edges
        ]
        if len(output_logic) != 1:
            test.error("Missing published output connection for " + instance)
    if "i_fallback->__Vdly__state" not in parent_sched:
        test.error("Ineligible child procedure did not remain on the fallback path")

child_graphs = test.glob_some(test.obj_dir + "/*nba_subgraph_pre_*_orderg_pre.dot")
parent_graphs = test.glob_some(test.obj_dir + "/*nba_orderg_pre.dot")
parent_acyc_graphs = test.glob_some(test.obj_dir + "/*nba_orderg_acyc.dot")
if len(child_graphs) != 5:
    test.error("Expected five child Order graphs, got " + str(len(child_graphs)))
if len(parent_graphs) != 1:
    test.error("Expected one parent NBA Order graph, got " + str(len(parent_graphs)))
if len(parent_acyc_graphs) != 1:
    test.error("Expected one acyclic parent NBA Order graph, got " + str(len(parent_acyc_graphs)))
test.file_grep_any(child_graphs, r'__Vdly__state')
test.file_grep_any(child_graphs, r'__Vdly__q')
test.file_grep_count(parent_graphs[0], r'shape=doubleoctagon', 5)

with open(parent_graphs[0], 'r', encoding='utf8') as fh:
    graph = fh.read()

nodes = dict(re.findall(r'^\s*n(\d+)\s+\[.*label="(.*?)", color=', graph, re.MULTILINE))
edges = set(re.findall(r'^\s*n(\d+) -> n(\d+)', graph, re.MULTILINE))
with open(parent_acyc_graphs[0], 'r', encoding='utf8') as fh:
    acyclic_edges = set(re.findall(r'^\s*n(\d+) -> n(\d+)', fh.read(), re.MULTILINE))


def find_node(instance, variable, marker):
    matches = []
    for node, label in nodes.items():
        if instance + "->" + variable not in label:
            continue
        prefix = label.split(r'\n', 1)[0]
        if marker is None:
            if all(word not in prefix for word in ('PRE', 'POST', 'PORD', 'PHASE')):
                matches.append(node)
        elif marker in prefix:
            matches.append(node)
    if len(matches) != 1:
        test.error("Expected one {} {} node, got {}".format(instance, variable, matches))
    return matches[0]


for instance in boundary_cases:
    published_post = find_node(instance, '__VsubgraphPublished__0', 'POST')
    published_value = find_node(instance, '__VsubgraphPublished__0', None)
    commits = [
        target for source, target in edges
        if source == published_post and 'ALWAYSPOST' in nodes.get(target, '')
    ]
    if len(commits) != 1 or (commits[0], published_value) not in edges:
        test.error("Missing output commit for " + instance)
    captured = [
        node for node, label in nodes.items() if instance + '->__VsubgraphCapture__' in label
    ]
    if not captured:
        test.error("Missing captured inputs for " + instance)
    if instance == 'i_ring_a' and len(captured) != 4:
        test.error("Expected four distinct ring_a captures, got " + str(len(captured)))
    capture_writers = []
    for saved in captured:
        writers = [
            source for source, target in edges
            if target == saved and 'ALWAYS' in nodes.get(source, '')
        ]
        capture_writers.extend(writers)
        consumers = [
            target for source, target in edges
            if source == saved and 'ACTIVE' in nodes.get(target, '')
        ]
        required = {(writer, saved) for writer in writers}
        required.update((saved, consumer) for consumer in consumers)
        if len(writers) != 1 or len(consumers) != 1 \
                or not required.issubset(edges & acyclic_edges):
            test.error("Missing uncut capture/evaluate dependency for {} {}".format(
                instance, nodes[saved]))
    if instance == 'i_ring_a':
        for source_instance, source_var in (('i_serial0', '__VsubgraphPublished__0'),
                                            ('i_ring_b', '__VsubgraphPublished__0'), ('TOP',
                                                                                      'parent_q')):
            old_value_post = find_node(source_instance, source_var, 'POST')
            if not any((writer, old_value_post) in acyclic_edges for writer in capture_writers):
                test.error("Missing old-value capture before publish for {} {}".format(
                    source_instance, source_var))

phase_nodes = [node for node, label in nodes.items() if 'PHASE' in label.split(r'\n', 1)[0]]
if len(phase_nodes) != len(boundary_cases):
    test.error("Expected one operation-stage token per eligible boundary")
for phase in phase_nodes:
    evaluators = [
        source for source, target in edges
        if target == phase and 'ACTIVE' in nodes.get(source, '')
    ]
    commits = [
        target for source, target in edges
        if source == phase and 'ALWAYSPOST' in nodes.get(target, '')
    ]
    if len(evaluators) != 1 or len(commits) != 1 \
            or (evaluators[0], phase) not in acyclic_edges \
            or (phase, commits[0]) not in acyclic_edges:
        test.error("Missing uncut evaluate-before-commit dependency")

for instance in boundary_cases:
    if any(instance + '->__Vdly__' in label or instance + '->__PVT__state' in label
           for label in nodes.values()):
        test.error("Child implementation state leaked into parent Order: " + instance)

test.passes()
