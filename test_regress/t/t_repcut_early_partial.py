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
import os
import random
import re
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
base = test.obj_dir + '/' + test.vm_prefix + '__repcut_early'
# Unsupported procedures and feedback stay in native scheduling. Their
# boundaries do not make the supported candidate-kernel graph incomplete.
test.verilator_flags += ['-fno-dfg', '-fno-gate']
for define in ('', 'REPCUT_CYCLE', 'REPCUT_DOMAIN', 'REPCUT_GATED_CLOCK', 'REPCUT_INVERTED_CLOCK',
               'REPCUT_CLOCK_CYCLE', 'REPCUT_CLOCK_WRITERS', 'REPCUT_MEM_WRITERS',
               'REPCUT_ROM_BLOCKING', 'REPCUT_ROM_UNINITIALIZED', 'REPCUT_MEM_BOUNDS',
               'REPCUT_INPUT_INIT', 'REPCUT_COND_INIT', 'REPCUT_INIT_WRITERS', 'REPCUT_EFFECT'):
    test.compile(verilator_make_gmake=False,
                 verilator_flags2=[
                     '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical', '-Wno-UNOPTFLAT',
                     '-Wno-MULTIDRIVEN'
                 ] + (['+define+' + define] if define else []))
    report = Path(base + '.report.txt').read_text(encoding="utf8")
    assert 'complete 1\n' in report, (define, report)
    assert os.path.exists(base + '.graph')
    assert not os.path.exists(base + '.partial')
    if define == 'REPCUT_DOMAIN':
        assert 'domains 2\n' in report
    if not define or define == 'REPCUT_ROM_BLOCKING':
        assert 'native_retained ' in report, report

# A supported RAM keeps reads on old memory and writes as independent sinks.
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical',
                 '+define+REPCUT_MEMORY'
             ])
assert 'complete 1' in Path(base + '.report.txt').read_text(encoding="utf8")
rows = list(
    csv.DictReader(io.StringIO(Path(base + '.nodes.tsv').read_text(encoding="utf8")),
                   delimiter='\t'))
nodes = {int(row['id']): row for row in rows}
for node in nodes.values():
    node['inputs'] = [int(i) for i in node['inputs'].split(',') if i]
bindings = {
    int(row['id']): row
    for row in csv.DictReader(io.StringIO(Path(base + '.bindings.tsv').read_text(encoding="utf8")),
                              delimiter='\t')
}
ports = sorted((i for i in nodes if nodes[i]['kind'] == 'MEMWRITE'),
               key=lambda i: int(bindings[i]['priority']))
for i in ports:
    assert int(bindings[i]['priority']) == int(nodes[i]['label'].split('#')[-1])
    assert bindings[i]['storage'] == bindings[nodes[i]['inputs'][0]]['storage']
    assert bindings[i]['domain'] == '0'
assert len({bindings[i]['storage'] for i in ports}) == 1
next_values = [i for i in nodes if nodes[i]['kind'] == 'NEXT']
assert len(ports) == 3, 'Memory write ports must not be collapsed'
assert len(next_values) == 1
graph_lines = Path(base + '.graph').read_text(encoding="utf8").splitlines()[1:]
assert all(len(graph_lines[i].split()) == 2
           for i in ports), 'A write must not feed another operation'


def evaluate_memory(index, values, cache):
    if index in cache:
        return cache[index]
    node = nodes[index]
    kind = node['kind']
    args = [evaluate_memory(i, values, cache) for i in node['inputs']]
    if kind == 'OLDMEM':
        result = values['mem']
    elif kind == 'INIT':
        result = values['xvalue']
    elif kind in ('OLD', 'INPUT'):
        result = values[node['label'].split('->')[-1]]
    elif kind == 'CONST':
        match = re.fullmatch(r"\d+'s?([hbod])([0-9a-fA-F_]+)", node['label'])
        assert match, node
        result = int(match[2].replace('_', ''), {'h': 16, 'b': 2, 'o': 8, 'd': 10}[match[1]])
    elif kind in ('VAR', 'NEXT', 'OUTPUT'):
        result = args[0]
    elif kind == 'MEMREAD':
        result = args[0][args[1]]
    elif kind == 'MEMWRITE':
        result = (args[1], args[2], args[3])
    elif kind == 'SEL':
        result = args[0] >> args[1]
    elif kind == 'XOR':
        result = args[0] ^ args[1]
    elif kind == 'LOGAND':
        result = int(bool(args[0]) and bool(args[1]))
    elif kind == 'LOGNOT':
        result = int(not args[0])
    elif kind == 'BRANCH':
        result = int(bool(args[0]))
    elif kind == 'LTE':
        result = int(args[0] <= args[1])
    elif kind == 'GTE':
        result = int(args[0] >= args[1])
    elif kind in ('COND', 'JOIN'):
        result = args[1] if args[0] else args[2]
    else:
        raise AssertionError('Unexpected memory operation: ' + kind)
    if isinstance(result, int):
        result &= (1 << int(node['width'])) - 1
    cache[index] = result
    return result


rng = random.Random(73)
for address in range(4):
    for data in range(256):
        old_memory = [rng.randrange(256) for _ in range(4)]
        values = {'mem': old_memory, 'addr': address, 'data': data, 'value': 0}
        cache = {}
        writes = [evaluate_memory(i, values, cache) for i in ports]
        observed = evaluate_memory(next_values[0], values, cache)
        updated = old_memory.copy()
        for enabled, target, word in writes:
            if enabled:
                updated[target] = word
        expected = old_memory.copy()
        expected[address] = data
        if data & 1:
            if data & 2:
                expected[2] = old_memory[address] ^ data
            else:
                expected[1] = data
        assert observed == old_memory[address], 'Read saw a same-edge write'
        assert updated == expected, 'Write priority or enable was lost'

# Each memory port may have its own evaluation owner; publication stays exclusive.
dependencies = {i: node['inputs'].copy() for i, node in nodes.items()}
for control in csv.DictReader(io.StringIO(Path(base + '.controls.tsv').read_text(encoding="utf8")),
                              delimiter='\t'):
    dependencies[int(control['node'])].append(int(control['predicate']))
sinks = [i for i, node in nodes.items() if node['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE')]
partitions = [set(), set()]
for ordinal, sink in enumerate(ports + [i for i in sinks if i not in ports]):
    members = partitions[ordinal % 2]
    pending = [sink]
    while pending:
        i = pending.pop()
        if i not in members:
            members.add(i)
            pending.extend(dependencies[i])
membership = Path(test.obj_dir) / 'memory-membership.csv'
membership.write_text(''.join(','.join(map(str, sorted(p, reverse=True))) + ',\n'
                              for p in partitions),
                      encoding="utf8")
test.compile(verilator_make_gmake=False,
             threads=2,
             verilator_flags2=[
                 '-frepcut', '--repcut-partitioner',
                 partitioner(test, membership), '--no-skip-identical', '+define+REPCUT_MEMORY'
             ])
owners = {
    int(row['node']): row
    for row in csv.DictReader(io.StringIO(Path(base + '.owners.tsv').read_text(encoding="utf8")),
                              delimiter='\t')
}
assert {owners[i]['evaluation_owner'] for i in ports} == {'0', '1'}
assert {owners[i]['publication_owner'] for i in ports} == {'native'}
assert [int(owners[i]['publication_order']) for i in ports] == [0, 1, 2]

# Non-power-of-two memories keep language-level X behavior while every eager
# physical read remains in bounds and invalid writes remain disabled.
test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical',
                 '+define+REPCUT_MEMORY_ODD'
             ])
assert 'complete 1' in Path(base + '.report.txt').read_text(encoding="utf8")
rows = list(
    csv.DictReader(io.StringIO(Path(base + '.nodes.tsv').read_text(encoding="utf8")),
                   delimiter='\t'))
nodes = {int(row['id']): row for row in rows}
for node in nodes.values():
    node['inputs'] = [int(i) for i in node['inputs'].split(',') if i]
ports = [i for i in nodes if nodes[i]['kind'] == 'MEMWRITE']
next_values = [i for i in nodes if nodes[i]['kind'] == 'NEXT']
assert len(ports) == len(next_values) == 1
assert sum(n['kind'] == 'INIT' for n in nodes.values()) == 1
for address in range(4):
    for data in range(256):
        old_memory = [rng.randrange(256) for _ in range(3)]
        poison = rng.randrange(256)
        values = {'mem': old_memory, 'addr': address, 'data': data, 'value': 0, 'xvalue': poison}
        cache = {}
        observed = evaluate_memory(next_values[0], values, cache)
        enabled, target, word = evaluate_memory(ports[0], values, cache)
        assert observed == (old_memory[address] if address < 3 else poison)
        updated = old_memory.copy()
        if enabled:
            updated[target] = word
        expected = old_memory.copy()
        if address < 3:
            expected[address] = data
        assert updated == expected, 'Invalid memory write was not suppressed'

test.compile(verilator_make_gmake=False,
             verilator_flags2=[
                 '-fno-repcut', '--repcut-dump-graph', '--no-skip-identical',
                 '+define+REPCUT_CONSTANT_INIT'
             ])
assert 'complete 1' in Path(base + '.report.txt').read_text(encoding="utf8")
rows = list(
    csv.DictReader(io.StringIO(Path(base + '.nodes.tsv').read_text(encoding="utf8")),
                   delimiter='\t'))
nodes = {int(row['id']): row for row in rows}
for node in nodes.values():
    node['inputs'] = [int(i) for i in node['inputs'].split(',') if i]
outputs = [i for i in nodes if nodes[i]['kind'] == 'OUTPUT']
assert len(outputs) == 1, 'An output referenced only during startup must remain visible'
assert evaluate_memory(outputs[0], {}, {}) == 0x5a

test.passes()
