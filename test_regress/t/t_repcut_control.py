#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
import json
import random
import subprocess
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.verilator_flags += ['-fno-gate']
test.top_filename = str(Path(test.top_filename).resolve())
flags = [
    '--no-skip-identical', '--x-assign', '0', '--x-initial', '0', '--output-split-cfuncs', '32',
    '--output-split', '256'
]
test.compile(make_main=False,
             verilator_make_gmake=False,
             threads=2,
             verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph', '-fno-dfg'])
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
assert 'complete 1' in base.with_suffix('.report.txt').read_text(encoding="utf8")


def table(suffix, key='id'):
    with base.with_suffix(suffix).open(encoding="utf8") as stream:
        return {int(row[key]): row for row in csv.DictReader(stream, delimiter='\t')}


nodes = table('.nodes.tsv')
bindings = table('.bindings.tsv')
storage = table('.storage.tsv')
regions = table('.regions.tsv')
controls = table('.controls.tsv', 'node')
for i, node in nodes.items():
    node['inputs'] = [int(x) for x in node['inputs'].split(',') if x]
    node['dependencies'] = node['inputs'] + ([int(controls[i]['predicate'])]
                                             if i in controls else [])
assert any(r['parent'] for r in regions.values())
assert any(n['kind'] == 'JOIN' for n in nodes.values())
assert any(n['kind'] == 'COND' for n in nodes.values())
assert any(n['kind'] == 'MUL' and i in controls for i, n in nodes.items())
assert any(n['kind'] == 'MEMREAD' and i in controls for i, n in nodes.items())
# A shared combinational definition stays outside branches that consume it.
shared = [i for i, n in nodes.items() if n['label'].endswith('__DOT__shared_sum')]
assert shared and all(i not in controls for i in shared)
for i, control in controls.items():
    region = regions[int(control['region'])]
    assert (control['predicate'], control['taken']) == (region['predicate'], region['taken'])
for region in regions.values():
    predicate = int(region['predicate'])
    assert nodes[predicate]['kind'] == 'BRANCH'
    assert controls.get(predicate, {}).get('region', '') == region['parent']


def evaluator(values):
    cache = {}

    def active(region_id):
        region = regions[region_id]
        if region['parent'] and not active(int(region['parent'])):
            return False
        return bool(evaluate(int(region['predicate']))) == bool(int(region['taken']))

    def evaluate(i):
        if i in cache:
            return cache[i]
        node = nodes[i]
        kind = node['kind']
        assert i not in controls or active(int(controls[i]['region'])), (i, kind, 'inactive value')
        inputs = node['inputs']
        if kind in ('COND', 'JOIN'):
            result = evaluate(inputs[1 if evaluate(inputs[0]) else 2])
        elif kind in ('OLD', 'INPUT', 'OLDMEM'):
            name = storage[int(
                bindings[i]['storage'])]['label'].split('->')[-1].split('__DOT__')[-1]
            result = values[name]
            if kind == 'OLDMEM':
                return result
        elif kind == 'CONST':
            result = sum(int(w) << (32 * j) for j, w in enumerate(bindings[i]['words'].split(',')))
        elif kind == 'LOGAND':
            result = bool(evaluate(inputs[0])) and bool(evaluate(inputs[1]))
        elif kind == 'LOGOR':
            result = bool(evaluate(inputs[0])) or bool(evaluate(inputs[1]))
        else:
            args = [evaluate(j) for j in inputs]
            if kind in ('VAR', 'NEXT', 'OUTPUT', 'EXTEND'):
                result = args[0]
            elif kind in ('BRANCH', 'REDOR'):
                result = bool(args[0])
            elif kind == 'LOGNOT':
                result = not args[0]
            elif kind == 'NOT':
                result = ~args[0]
            elif kind == 'ADD':
                result = args[0] + args[1]
            elif kind == 'SUB':
                result = args[0] - args[1]
            elif kind == 'MUL':
                result = args[0] * args[1]
            elif kind == 'XOR':
                result = args[0] ^ args[1]
            elif kind == 'AND':
                result = args[0] & args[1]
            elif kind == 'OR':
                result = args[0] | args[1]
            elif kind == 'LTE':
                result = args[0] <= args[1]
            elif kind == 'GTE':
                result = args[0] >= args[1]
            elif kind == 'SEL':
                result = args[0] >> args[1]
            elif kind == 'SHIFTRS':
                width = int(nodes[inputs[0]]['width'])
                signed = args[0] - (1 << width) if args[0] & (1 << (width - 1)) else args[0]
                result = signed >> args[1]
            elif kind == 'MEMREAD':
                assert 0 <= args[1] < len(args[0])
                result = args[0][args[1]]
            else:
                raise AssertionError(kind)
        cache[i] = int(result) & ((1 << int(node['width'])) - 1)
        return cache[i]

    return evaluate, active


sinks = [i for i, n in nodes.items() if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE')]
next_q = next(i for i in sinks if nodes[i]['kind'] == 'NEXT' and '->q@' in nodes[i]['label'])
next_wq = next(i for i in sinks if nodes[i]['kind'] == 'NEXT' and '->wq@' in nodes[i]['label'])
outputs = {nodes[i]['label'].split('->')[-1]: i for i in sinks if nodes[i]['kind'] == 'OUTPUT'}
writes = sorted((i for i in sinks if nodes[i]['kind'] == 'MEMWRITE'),
                key=lambda i: int(bindings[i]['priority']))
rng = random.Random(23)
for sample in range(1024):
    values = {name: rng.randrange(128) for name in ('a', 'b', 'q')}
    values.update({name: rng.getrandbits(95) for name in ('wa', 'wb', 'wq')})
    values.update(mode=sample % 8,
                  en=rng.randrange(2),
                  select=rng.randrange(2),
                  reset=rng.randrange(2),
                  rd=rng.randrange(4),
                  wr=rng.randrange(4),
                  mem=[rng.randrange(128) for _ in range(3)])
    evaluate, active = evaluator(values)
    a, b, q = (values[n] for n in ('a', 'b', 'q'))
    total = (a + b) & 127
    y = ((total ^ a) + b if values['en'] else b -
         a) if values['mode'] else (a * b if values['select'] else a ^ b)
    expected_q = (total ^ q if values['en'] else q + b) if values['mode'] else q
    expected_q = 0 if values['reset'] else a if values['select'] else expected_q
    expected_data = (values['mem'][values['rd']] if values['rd'] < 3 else 0) if values['en'] else b
    assert evaluate(outputs['y']) == y & 127
    assert evaluate(outputs['observed_y']) == (y ^ q) & 127
    expected_wide = (values['wa'] ^ values['wb']) if values['select'] else (values['wa']
                                                                            & values['wb'])
    assert evaluate(outputs['wide_result']) == expected_wide
    term = ((a ^ b) + 0x13) & 127
    assert evaluate(outputs['local_result']) == ((term & a) ^ (term + b)) & 127
    assert evaluate(outputs['data']) == (expected_data if values['mode'] else a)
    assert evaluate(next_q) == expected_q & 127
    signed_wa = values['wa'] - (1 << 95) if values['wa'] & (1 << 94) else values['wa']
    expected_wq = ((signed_wa >> 3) + values['wb']) if values['en'] else values['wq']
    assert evaluate(next_wq) == (0 if values['reset'] else expected_wq) & ((1 << 95) - 1)
    memory = values['mem'].copy()
    for i in writes:
        if i in controls and not active(int(controls[i]['region'])):
            continue
        args = nodes[i]['inputs']
        if evaluate(args[1]):
            memory[evaluate(args[2])] = evaluate(args[3])
    expected_memory = values['mem'].copy()
    if values['mode']:
        address = values['wr'] if values['en'] else values['rd']
        if address < 3:
            expected_memory[address] = (a
                                        ^ b if values['select'] else total) if values['en'] else a
    assert memory == expected_memory

parts = [set(), set()]
for ordinal, sink in enumerate(sinks):
    pending = [sink]
    part = parts[ordinal % 2]
    while pending:
        i = pending.pop()
        if i not in part:
            part.add(i)
            pending.extend(nodes[i]['dependencies'])
assert any(nodes[i]['kind'] == 'BRANCH' for i in parts[0] & parts[1]), 'No replicated predicate'
membership = Path(test.obj_dir) / 'membership.csv'
membership.write_text(''.join(','.join(map(str, sorted(p))) + ',\n' for p in parts),
                      encoding="utf8")


def check_chunk_boundaries():  # pylint: disable=too-many-locals
    # Check the final native kernel and compare its bounded helper functions
    # with the planned boundaries and their live-value costs.
    dump = test.glob_one(test.obj_dir + '/' + test.vm_prefix + '*_final.tree.json')
    pending = [json.loads(Path(dump).read_text(encoding="utf8"))]
    functions = {}
    while pending:
        node = pending.pop()
        if isinstance(node, dict):
            if node.get('isRepCut'):
                functions[node['addr']] = node
            pending.extend(node.values())
        elif isinstance(node, list):
            pending.extend(node)
    assert functions, 'Missing RepCut functions in the final AST'
    with base.with_suffix('.chunks.tsv').open(encoding="utf8") as stream:
        chunks = {
            r['function']: int(r['body_nodes'])
            for r in csv.DictReader(stream, delimiter='\t')
        }
    assert all(size <= 32 for size in chunks.values())
    with base.with_suffix('.cuts.tsv').open(encoding="utf8") as stream:
        groups = {}
        for row in csv.DictReader(stream, delimiter='\t'):
            groups.setdefault(row['group'], []).append(row)
    assert groups, 'No compilation-boundary diagnostics'
    ordinals = {}
    for rows in groups.values():
        prefix = [int(r['prefix_nodes']) for r in rows]
        costs = [int(r['live_bytes']) for r in rows]
        selected = [int(r['boundary']) for r in rows if r['selected_cut'] == '1']
        greedy = [int(r['boundary']) for r in rows if r['greedy_cut'] == '1']
        assert [int(r['boundary']) for r in rows] == list(range(len(rows)))
        assert prefix[0] == 0 and all(prefix[i] < prefix[i + 1] for i in range(len(prefix) - 1))
        assert costs[0] == costs[-1] == 0
        assert len(selected) == len(greedy), 'Chunk planning increased function count'
        assert selected[-1] == greedy[-1] == len(rows) - 1
        assert sum(costs[i] for i in selected) <= sum(costs[i] for i in greedy)
        if rows[0]['analyzed'] == '0':
            assert selected == greedy, 'Opaque accesses must keep greedy boundaries'
        tag = rows[0]['function']
        begin = 0
        for end in selected:
            size = prefix[end] - prefix[begin]
            assert 0 < size <= 32
            ordinal = ordinals.get(tag, 0)
            assert chunks[tag + '__chunk' + str(ordinal)] == size, \
                'Constructed function disagrees with its planned boundary'
            ordinals[tag] = ordinal + 1
            begin = end


for repcut, dfg, localize, threads in ((False, True, True, 2), (True, True, True, 2),
                                       (True, False, True, 2), (True, True, False, 2),
                                       (True, True, True, 1), (True, False, True, 1)):
    mode_flags = ['-frepcut', '--repcut-partitioner',
                  partitioner(test, membership)] if repcut else []
    if repcut:
        mode_flags += ['--dump-tree-json', '--stats', '--debug-self-test']
    if not dfg:
        mode_flags += ['-fno-dfg']
    if not localize:
        # Keep optimizer-created temporaries in model storage so the late writer
        # audit exercises ownership propagation, even on this small fixture.
        mode_flags += ['-fno-localize']
    if repcut:
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags +
                     [f'-f{"" if dfg else "no-"}dfg', '-fno-repcut', '--repcut-dump-graph'])
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            current = list(csv.DictReader(stream, delimiter='\t'))
        deps = [[int(x) for x in n['inputs'].split(',') if x] for n in current]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                deps[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        for ordinal, n in enumerate(current):
            if n['kind'] not in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT', 'CALLBACK'):
                continue
            pending = [int(n['id'])]
            part = parts[ordinal % threads]
            while pending:
                node = pending.pop()
                if node not in part:
                    part.add(node)
                    pending.extend(deps[node])
        membership.write_text(''.join(','.join(map(str, sorted(p))) + '\n' for p in parts),
                              encoding="utf8")
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + mode_flags +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    if repcut:
        check_chunk_boundaries()
    subprocess.run(
        ['make', '-C',
         str(Path(test.obj_dir).resolve()), '-f', test.vm_prefix + '.mk', '-j2'],
        check=True)
    test.execute()
    for pch in Path(test.obj_dir).glob(test.vm_prefix + '__pch.h.*.gch'):
        pch.unlink()
test.passes()
