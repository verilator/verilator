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
import re
import subprocess
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = str(Path(test.top_filename).resolve())
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
membership = Path(test.obj_dir) / 'membership.csv'
cases = [('stock', 2, [], 0), ('default', 2, [], 1), ('default4', 4, [], 1), ('serial', 1, [], 0),
         ('skew', 2, [], 1), ('protect', 2, ['--protect-ids', '-Wno-INSECURE'], 1),
         ('guard-stock', 2, [], 0), ('guard-default', 4, [], 1),
         ('guard-protect', 4, ['--protect-ids', '-Wno-INSECURE'], 1)]
# Exercise the bounded conditional path before the ordinary-policy cases.
cases = [c for c in cases if c[0].startswith('guard')
         ] + [c for c in cases if not c[0].startswith('guard')]
reference = str(Path(test.obj_dir).resolve() / 'stock.vcd')
for case, threads, options, expected in cases:
    conditional = case.startswith('guard')
    flags = [
        '--trace-vcd', '--stats', '--debug-check', '--no-skip-identical', '--x-initial', '0',
        '--x-assign', '0', '--output-split-cfuncs', '256'
    ]
    if conditional:
        flags += ['-GCONDITIONAL=1', '-fno-table', '--output-split-cfuncs', '32']
    if case == 'default':
        flags += ['--dumpi-tree', '3', '--dumpi-tree-json', '3']
    runtime = ['-fno-repcut']
    if not case.endswith('stock'):
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        deps = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                deps[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        ordinal = 0
        for n in nodes:
            if n['kind'] not in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT'):
                continue
            owner = ordinal % threads
            ordinal += 1
            if n['kind'] == 'NEXT' and 'wide_a' in n['label']:
                index = int(re.search(r'__BRA__(\d+)__', n['label'])[1])
                owner = (index // 2 if conditional else index) % threads
            if n['kind'] == 'NEXT' and 'auxiliary' in n['label']:
                owner = 0 if conditional else threads - 1
            if n['kind'] == 'MEMWRITE' and conditional:
                owner = 1
            if n['kind'] == 'NEXT' and 'narrow' in n['label']:
                owner = 0
            if n['kind'] == 'NEXT' and 'wide_c' in n['label']:
                owner = 1 if case == 'skew' and '__BRA__127__' in n['label'] else 0
            pending = [int(n['id'])]
            while pending:
                node = pending.pop()
                if node not in parts[owner]:
                    parts[owner].add(node)
                    pending.extend(deps[node])
        assert set().union(*parts) == set(range(len(nodes)))
        membership.write_text(''.join(','.join(map(str, sorted(p))) + '\n' for p in parts),
                              encoding="utf8")
        runtime = ['--repcut', '--repcut-partitioner', partitioner(test, membership)] + options
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    # A parallel publication report is insufficient: the runtime's generic
    # small-graph policy must not silently execute the phase on the caller.
    # Probe actual dispatcher entry without enabling profiling (which itself
    # disables the serial fast path), including protected generated names.
    dispatches = []
    if threads > 1:
        for path in Path(test.obj_dir).glob('*__ExecGraph__Slow.cpp'):
            for graph, body in re.findall(r'VlExecGraph (\w+)\{(.*?)\n};',
                                          path.read_text(encoding='utf8'), re.DOTALL):
                match = re.search(r'&(\w+),\s*(\w+)\s*$', body)
                assert match
                if graph.endswith('_publish') or match[2] == '0':
                    dispatches.append(match[1])
    assert len(dispatches) == expected, (case, dispatches)
    for function in dispatches:
        found = 0
        pattern = re.compile(r'(void ' + re.escape(function) + r'\([^)]*\) \{)')
        for path in Path(test.obj_dir).glob('*.cpp'):
            text = path.read_text(encoding='utf8')
            text, count = pattern.subn(r'\1\n    repcutParallelPublicationSeen();', text)
            if count:
                path.write_text('extern void repcutParallelPublicationSeen();\n' + text,
                                encoding='utf8')
                found += count
        assert found == 1, function
    if case == 'default':
        tree = max(map(Path, test.glob_some(test.obj_dir + '/*_sched.tree.json')),
                   key=lambda path: path.stat().st_mtime_ns)
        pending = [json.loads(tree.read_text(encoding='utf8'))]
        graphs = []
        while pending:
            node = pending.pop()
            if isinstance(node, dict):
                if node.get('type') == 'EXECGRAPH':
                    graphs.append(node)
                pending.extend(node.values())
            elif isinstance(node, list):
                pending.extend(node)
        assert graphs
        assert sum(bool(graph.get('forceParallel')) for graph in graphs) == expected
        assert any(not graph.get('forceParallel') for graph in graphs)
    if not case.endswith('stock'):
        with base.with_suffix('.publication.tsv').open(encoding="utf8") as stream:
            rows = list(csv.DictReader(stream, delimiter='\t'))
        domains = {r['domain']: r for r in rows}
        assert len(domains) == 3
        assert sum(r['decision'] == 'parallel' for r in domains.values()) == expected, rows
        if case in ('default', 'default4', 'protect', 'skew'):
            assert {r['mode'] for r in rows} == {'auto'}
            reasons = {r['reason'] for r in rows}
            assert 'estimated-benefit' in reasons and 'dispatch-cost' in reasons
            assert ('owner-imbalance' if case == 'skew' else 'one-owner') in reasons
            if case == 'skew':
                assert 'owner-imbalance' in reasons
        if case == 'serial':
            assert {r['reason'] for r in rows} == {'single-thread'}
        stats = Path(test.stats).read_text(encoding="utf8")
        guarded = re.search(r'RepCut native publication, guarded dispatches\s+(\d+)', stats)
        expected_guards = expected if conditional else 0
        assert (int(guarded[1]) if guarded else 0) == expected_guards, case
        if conditional:
            helpers = re.search(r'RepCut native publication, dispatch enable helpers\s+(\d+)',
                                stats)
            assert helpers and int(helpers[1]) == 13, case
        (Path(test.obj_dir) / (case + '.stats')).write_text(stats, encoding="utf8")
        (Path(test.obj_dir) / (case + '.publication.tsv')).write_text(
            base.with_suffix('.publication.tsv').read_text(encoding="utf8"), encoding="utf8")
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    trace = str(Path(test.obj_dir).resolve() / (case + '.vcd'))
    result = subprocess.run([
        str(Path(test.obj_dir).resolve() / test.vm_prefix), trace,
        str(threads),
        str(int(conditional)),
        str(int(expected != 0))
    ],
                            capture_output=True,
                            text=True,
                            timeout=60,
                            check=False)
    output = result.stdout + result.stderr
    (Path(test.obj_dir) / (case + '.log')).write_text(output, encoding="utf8")
    if result.returncode:
        test.error(case + ': ' + output)
    assert '*-* All Finished *-*' in output
    if not case.endswith(('stock', 'protect')):
        test.trace_identical(
            trace,
            str(Path(test.obj_dir).resolve() / 'guard-stock.vcd') if conditional else reference)
test.passes()
