#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
# Reuse the varying-input decoder checks, including inverted comparisons and
# hierarchy. Native decoder tables must preserve their scheduling boundaries.
test.top_filename = str(Path('t/t_dfg_bin_to_one_hot.v').resolve())
flags = ['--stats', '--no-skip-identical', '-fno-table', '-fno-inline']
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')

for mode in ('stock', 'stock_graph', 'default', 'serial', 'fallback', 'protected', 'trace'):
    threads = 1 if mode in ('stock', 'stock_graph', 'serial') else 2
    options = flags + (['--protect-ids', '--protect-key', 'REPCUT_DECODERS']
                       if mode == 'protected' else [])
    if mode == 'trace':
        options += ['--trace']
    if mode == 'fallback':
        options += ['--output-split-cfuncs', '64']
    if mode == 'stock_graph':
        options += ['-fno-repcut', '--repcut-dump-graph']
    runtime = ['-fno-repcut']
    if not mode.startswith('stock'):
        test.compile(verilator_make_gmake=False,
                     threads=threads,
                     context_threads=threads,
                     trace=mode == 'trace',
                     verilator_flags2=options + ['-fno-repcut', '--repcut-dump-graph'])
        test.file_grep(base.with_suffix('.report.txt'), r'complete 1')
        report = base.with_suffix('.report.txt').read_text(encoding="utf8")
        assert 'native_retained memory write shape:' in report, mode
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        dependencies = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'EFFECT')]
        assert sinks
        for ordinal, sink in enumerate(sinks):
            pending = [sink]
            part = parts[ordinal % threads]
            while pending:
                node = pending.pop()
                if node not in part:
                    part.add(node)
                    pending.extend(dependencies[node])
        membership = Path(test.obj_dir) / 'membership.csv'
        membership.write_text(''.join(','.join(map(str, sorted(p))) + '\n' for p in parts),
                              encoding="utf8")
        runtime = ['-frepcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(threads=threads,
                 context_threads=threads,
                 trace=mode == 'trace',
                 verilator_flags2=options + runtime)
    test.execute()
    stats = Path(test.stats).read_text(encoding="utf8")
    stats_path = Path(test.obj_dir) / (mode + '.stats')
    stats_path.write_text(stats, encoding="utf8")
    test.file_grep(stats_path, r'Optimizations, DFG, BinToOneHot, decoders created\s+(\d+)', 5)

test.passes()
