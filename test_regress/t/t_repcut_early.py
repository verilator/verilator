#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
import io
import random
import re
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
# Preserve the transitive clock aliases until RepCut extracts the graph.
test.verilator_flags += ['-fno-dfg', '-fno-gate', '-fno-coalesce']
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical', '--debug-self-test'
             ])

base = test.obj_dir + '/' + test.vm_prefix + '__repcut_early'
test.file_grep(base + '.report.txt', r'complete 1')
test.file_grep(base + '.report.txt', r'^raw_domains (\d+)$', 0)
test.file_grep(base + '.report.txt', r'^domains (\d+)$', 2)
rows = list(csv.DictReader(io.StringIO(test.file_contents(base + '.nodes.tsv')), delimiter='\t'))
nodes = {int(row['id']): row for row in rows}
for node in nodes.values():
    node['inputs'] = [int(n) for n in node['inputs'].split(',') if n]


def table(suffix):
    return {
        int(row['id']): row
        for row in csv.DictReader(io.StringIO(Path(base + suffix).read_text(encoding="utf8")),
                                  delimiter='\t')
    }


bindings = table('.bindings.tsv')
storage = table('.storage.tsv')
domains = table('.domains.tsv')
regions = table('.regions.tsv')
controls = {
    int(row['node']): row
    for row in csv.DictReader(io.StringIO(Path(base + '.controls.tsv').read_text(encoding="utf8")),
                              delimiter='\t')
}
assert regions and controls
for i, node in nodes.items():
    node['dependencies'] = node['inputs'].copy()
    if i in controls:
        control = controls[i]
        region = regions[int(control['region'])]
        assert control['predicate'] == region['predicate'] and control['taken'] == region['taken']
        node['dependencies'].append(int(control['predicate']))
for region in regions.values():
    predicate = int(region['predicate'])
    assert nodes[predicate]['kind'] == 'BRANCH'
    assert nodes[predicate]['width'] == '1'
    assert controls.get(predicate, {}).get('region', '') == region['parent']
assert any(region['parent'] for region in regions.values()), 'Nested control region lost'
assert set(bindings) == set(nodes)
assert len(domains) == 2
assert domains[0]['label'] == 'native:0'
assert domains[0]['clock_storage'] == domains[0]['posedge'] == ''
for i, node in nodes.items():
    binding = bindings[i]
    if node['kind'] in ('VAR', 'OLD', 'INPUT', 'INIT', 'NEXT', 'OUTPUT'):
        target = storage[int(binding['storage'])]
        assert target['label'] == node['label'].split('@')[0]
        assert target['width'] == node['width']
    if node['kind'] == 'NEXT':
        assert binding['domain'] in ('0', '1')
        old = [
            j for j in nodes
            if nodes[j]['kind'] == 'OLD' and bindings[j]['storage'] == binding['storage']
        ]
        assert len(old) == 1
    if node['kind'] == 'CONST':
        match = re.fullmatch(r"\d+'s?([hbod])([0-9a-fA-F_]+)", node['label'])
        expected = int(match[2].replace('_', ''), {'h': 16, 'b': 2, 'o': 8, 'd': 10}[match[1]])
        words = [int(w) for w in binding['words'].split(',')]
        assert sum(w << (32 * j) for j, w in enumerate(words)) == expected


def variable_name(node):
    return node['label'].split('@')[0].split('->')[-1]


def evaluate(index, inputs, cache):
    if index in cache:
        return cache[index]
    node = nodes[index]
    kind = node['kind']
    if index in controls:
        control = controls[index]
        # A lazy consumer must never reach a definition outside its active region.
        assert bool(evaluate(int(control['predicate']), inputs,
                             cache)) == bool(int(control['taken']))
    if kind in ('COND', 'JOIN'):
        condition = evaluate(node['inputs'][0], inputs, cache)
        result = evaluate(node['inputs'][1 if condition else 2], inputs, cache)
        cache[index] = result & ((1 << int(node['width'])) - 1)
        return cache[index]
    args = [evaluate(i, inputs, cache) for i in node['inputs']]
    if kind in ('OLD', 'INPUT'):
        assert not args, 'Old state must be independent of next-state writes'
        result = inputs[variable_name(node)]
    elif kind == 'CONST':
        result = sum(int(w) << (32 * j) for j, w in enumerate(bindings[index]['words'].split(',')))
    elif kind in ('VAR', 'NEXT', 'OUTPUT'):
        result = args[0]
    elif kind == 'ADD':
        result = args[0] + args[1]
    elif kind == 'BRANCH':
        result = bool(args[0])
    elif kind == 'XOR':
        result = args[0] ^ args[1]
    elif kind == 'SEL':
        result = args[0] >> args[1]
    elif kind == 'REPLICATE':
        width = int(nodes[node['inputs'][0]]['width'])
        result = sum(args[0] << (width * i) for i in range(args[1]))
    else:
        raise AssertionError('Unexpected graph operation: ' + kind)
    cache[index] = result & ((1 << int(node['width'])) - 1)
    return cache[index]


next_nodes = {variable_name(node): i for i, node in nodes.items() if node['kind'] == 'NEXT'}
assert set(next_nodes) == {'a', 'b'}, next_nodes
assert sum(node['kind'] == 'ADD' for node in nodes.values()) == 1
assert sum(node['kind'] == 'REPLICATE' for node in nodes.values()) == 1
output_nodes = {variable_name(node): i for i, node in nodes.items() if node['kind'] == 'OUTPUT'}

rng = random.Random(42)
for _ in range(1000):
    values = {name: rng.randrange(256) for name in ('a', 'b', 'x', 'y')}
    values.update({name: rng.randrange(2) for name in ('reset', 'en', 'force_b')})
    total = (values['x'] + values['y']) & 255
    expected_a = 0 if values['reset'] else ((total ^ values['b']) if values['en'] else values['a'])
    expected_b = 0 if values['reset'] else (total if values['force_b'] else values['a'])
    assert evaluate(next_nodes['a'], values, {}) == expected_a
    assert evaluate(next_nodes['b'], values, {}) == expected_b
    assert evaluate(output_nodes['repeated'], values, {}) == (values['x'] & 3) * 0x55
    assert evaluate(output_nodes['observation'], values, {}) == values['a'] ^ values['b']

# Exporting twice must not depend on node addresses or alter the graph.
before = {
    suffix: Path(base + suffix).read_text(encoding="utf8")
    for suffix in ('.nodes.tsv', '.bindings.tsv', '.storage.tsv', '.domains.tsv', '.regions.tsv',
                   '.controls.tsv')
}
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical', '--debug-self-test'
             ])
for suffix, contents in before.items():
    assert Path(base + suffix).read_text(encoding="utf8") == contents
# Return genuinely replicated cones, deliberately in reverse node order.
sinks = [i for i, node in nodes.items() if node['kind'] in ('NEXT', 'OUTPUT')]
partitions = [set(), set()]
for ordinal, sink in enumerate(sinks):
    pending = [sink]
    members = partitions[ordinal % 2]
    while pending:
        i = pending.pop()
        if i not in members:
            members.add(i)
            pending.extend(nodes[i]['dependencies'])
membership = Path(test.obj_dir) / 'membership.csv'
membership.write_text(''.join(','.join(map(str, sorted(p, reverse=True))) + ',\n'
                              for p in partitions),
                      encoding="utf8")
test.compile(verilator_make_gmake=False,
             threads=2,
             verilator_flags2=[
                 '-frepcut', '--repcut-partitioner',
                 partitioner(test, membership), '--no-skip-identical'
             ])
plan = list(
    csv.DictReader(io.StringIO(Path(base + '.plan.tsv').read_text(encoding="utf8")),
                   delimiter='\t'))
owners = {
    int(row['node']): row
    for row in csv.DictReader(io.StringIO(Path(base + '.owners.tsv').read_text(encoding="utf8")),
                              delimiter='\t')
}
assert set(owners) == set(sinks)
for part, members in enumerate(partitions):
    for phase, kinds in [('next', ('NEXT', )), ('native_output_reference', ('OUTPUT', ))]:
        expected = set()
        pending = [i for i in members if nodes[i]['kind'] in kinds]
        while pending:
            i = pending.pop()
            if i not in expected:
                expected.add(i)
                pending.extend(nodes[i]['dependencies'])
        rows = [r for r in plan if int(r['partition']) == part and r['phase'] == phase]
        seen = set()
        for ordinal, row in enumerate(rows):
            i = int(row['node'])
            assert int(row['ordinal']) == ordinal
            assert set(nodes[i]['dependencies']) <= seen, 'Evaluation must follow data and control'
            assert i not in seen
            seen.add(i)
        assert seen == expected
    for i in members & set(sinks):
        assert owners[i]['evaluation_owner'] == ('native'
                                                 if nodes[i]['kind'] == 'OUTPUT' else str(part))
        assert owners[i]['publication_owner'] == 'native'
# A fresh partitioner result must replace the previous ownership plan.
flags = ['-frepcut', '--repcut-partitioner', partitioner(test, membership), '--no-skip-identical']
membership.write_text(''.join(','.join(map(str, sorted(p))) + ',\n' for p in reversed(partitions)),
                      encoding="utf8")
test.compile(verilator_make_gmake=False, threads=2, verilator_flags2=flags)
changed_owners = list(
    csv.DictReader(io.StringIO(Path(base + '.owners.tsv').read_text(encoding="utf8")),
                   delimiter='\t'))
for row in changed_owners:
    previous = owners[int(row['node'])]['evaluation_owner']
    assert row['evaluation_owner'] == ('native' if previous == 'native' else str(1 -
                                                                                 int(previous)))
# An export-only rerun cannot leave an apparently accepted old plan behind.
for suffix in ('.chunks.tsv', '.cuts.tsv'):
    Path(base + suffix).write_text('stale compilation report', encoding="utf8")
test.compile(verilator_make_gmake=False,
             verilator_flags2=['-fno-repcut', '--repcut-dump-graph', '--no-skip-identical'])
assert not Path(base + '.plan.tsv').exists()
assert not Path(base + '.owners.tsv').exists()
assert not Path(base + '.chunks.tsv').exists()
assert not Path(base + '.cuts.tsv').exists()
test.passes()
