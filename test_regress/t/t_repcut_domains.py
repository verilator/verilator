#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import collections
import csv
import json
import subprocess
from pathlib import Path

import vltest_bootstrap
from repcut_common import clear_model_profiles, partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = str(Path(test.top_filename).resolve())
flags = [
    '--assert', '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0',
    '--output-split-cfuncs', '32', '--output-split', '256', '-fno-coalesce'
]
# Keep clock aliases until RepCut so this test exercises its sensitivity coalescing.
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
reference = {}


def check_shared_calls(path, expected):
    """Shared prefixes have one guarded call, including through outlined bodies."""

    def nodes(value):
        if isinstance(value, dict):
            yield value
            for child in value.values():
                yield from nodes(child)
        elif isinstance(value, list):
            for child in value:
                yield from nodes(child)

    tree = json.loads(path.read_text(encoding="utf8"))
    helpers = {
        node['addr']
        for node in nodes(tree) if node.get('type') == 'CFUNC' and node.get('repcutSharedOrder')
    }
    assert len(helpers) == expected, helpers
    calls = collections.Counter(node['funcp'] for node in nodes(tree)
                                if node.get('type') == 'CCALL' and node['funcp'] in helpers)
    assert calls == {helper: 1 for helper in helpers}, calls
    guarded = collections.Counter(
        call['funcp'] for node in nodes(tree)
        if node.get('type') == 'IF' and node['condp'][0]['type'] == 'TRIGGERED'
        for call in nodes(node['thensp'])
        if call.get('type') == 'CCALL' and call['funcp'] in helpers)
    assert guarded == calls, guarded


modes = (('stock', 1), ('serial', 1), ('parallel', 2), ('parallel4', 4), ('protected', 2),
         ('public', 2), ('no_gate', 2), ('shared_serial', 1), ('shared2', 2), ('shared4', 4),
         ('shared_protected', 2), ('shared_public', 2), ('shared_tiny', 2), ('shared_no_gate', 2))
modes += (('stock_large', 1), ('shared_large', 2), ('shared_large4', 4), ('shared_large_tiny', 2),
          ('shared_large_protected', 2), ('default_large', 2))
modes += (('shared_large_serial', 1), ('shared_large_serial_tiny', 1),
          ('shared_large_serial_protected', 1), ('shared_large_serial_public', 1))
modes += (('stock_large_observe', 1), ('shared_large_serial_observe', 1), ('shared_large_observe',
                                                                           2))
for mode, threads in modes:
    rounds = 8 if 'large' in mode else 0
    observe = mode.endswith('observe')
    options = flags + (['--protect-ids', '--protect-key', 'REPCUT_DOMAINS']
                       if mode.endswith('protected') else [])
    options += ['-GSHARED_ROUNDS=' + str(rounds), '-GOBSERVE_DPI=' + str(int(observe))]
    shared = mode.startswith(('shared', 'default'))
    limit = 128 if shared and 'tiny' not in mode else 32
    options += ['--output-split-cfuncs', str(limit)]
    if mode.endswith('public'):
        options += ['--public-flat-rw']
    if mode in ('no_gate', 'shared_no_gate') or rounds:
        options += ['-fno-gate']
    if mode in ('shared_large', 'shared_large_serial'):
        options += ['--dumpi-tree', '3', '--dumpi-tree-json', '3']
    runtime = ['-fno-repcut']
    if not mode.startswith('stock'):
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=options + ['-fno-repcut', '--repcut-dump-graph'])
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        dependencies = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [
            int(n['id']) for n in nodes
            if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT', 'CALLBACK')
        ]
        for ordinal, sink in enumerate(sinks):
            pending = [sink]
            part = parts[ordinal % threads]
            while pending:
                node = pending.pop()
                if node not in part:
                    part.add(node)
                    pending.extend(dependencies[node])
        membership = Path(test.obj_dir) / 'membership.csv'
        membership.write_text(''.join(','.join(map(str, sorted(p))) + ',\n' for p in parts),
                              encoding="utf8")
        runtime = ['-frepcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=options + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    clear_model_profiles(test)
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    result = subprocess.run([str(Path(test.obj_dir).resolve() / test.vm_prefix)],
                            capture_output=True,
                            text=True,
                            check=True,
                            timeout=30)
    output = result.stdout + result.stderr
    (Path(test.obj_dir) / (mode + '.log')).write_text(output, encoding="utf8")
    assert '*-* All Finished *-*' in output
    if mode.startswith('stock'):
        reference[rounds, observe] = output
    else:
        assert output == reference[rounds, observe], mode
        # Public aliases remain observable. Disabling gate optimization still
        # allows later native sensitivity coalescing; distinct events stay separate.
        preserve_aliases = mode.endswith('public')
        stats = Path(test.obj_dir) / (mode + '.stats')
        stats.write_text(Path(test.stats).read_text(encoding="utf8"), encoding="utf8")
        # Gate optimization coalesces one additional sensitivity in this design.
        test.file_grep(
            str(stats), r'RepCut native, domains\s+(\d+)', 16 if preserve_aliases else
            ((7 if '-fno-gate' in options else 6) + int(observe)))
        test.file_grep(str(stats), r'RepCut native, coalesced sensitivities\s+(\d+)',
                       0 if preserve_aliases else (9 if '-fno-gate' in options else 10))
        if not preserve_aliases and (threads > 1 or (shared and rounds)):
            test.file_grep(str(stats), r'RepCut native batch, dispatches\s+(\d+)', 1)
            if threads == 1:
                test.file_grep(str(stats), r'RepCut native batch, serial dispatches\s+(\d+)', 1)
            if shared and rounds:
                test.file_grep(str(stats), r'RepCut shared domains, factored helpers\s+(\d+)',
                               threads + 1)
                test.file_grep(str(stats),
                               r'RepCut shared domains, partitions above cost floor\s+(\d+)',
                               threads)
                if mode in ('shared_large', 'shared_large_serial'):
                    trees = test.glob_some(test.obj_dir + '/*_sched.tree.json')
                    check_shared_calls(
                        max(map(Path, trees), key=lambda path: path.stat().st_mtime_ns),
                        threads + 1)
            else:
                assert 'RepCut shared domains, factored helpers' not in stats.read_text(
                    encoding="utf8")
        if preserve_aliases or (threads == 1 and not rounds):
            assert 'RepCut native batch,' not in stats.read_text(encoding="utf8")
            assert 'RepCut shared domains, factored helpers' not in stats.read_text(
                encoding="utf8")
        with base.with_suffix('.chunks.tsv').open(encoding="utf8") as stream:
            chunks = list(csv.DictReader(stream, delimiter='\t'))
        # A small partition may fit entirely in its entry function. Both entry
        # functions and any required helpers must obey the construction budget.
        assert chunks
        assert all(int(row['body_nodes']) <= limit for row in chunks)
test.passes()
