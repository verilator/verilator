#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
import re
import subprocess
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = str(Path(test.top_filename).resolve())
flags = [
    '--assert', '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0',
    '--output-split-cfuncs', '32', '--output-split', '256', '-fno-table'
]
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
references = {}
for mode, threads in [('stock', 1), ('serial', 1), ('parallel', 2), ('parallel4', 4),
                      ('packing', 2), ('protected', 2), ('public', 2), ('trace', 2),
                      ('isolated_stock', 1), ('isolated', 2)]:
    options = flags[:]
    if mode == 'packing':
        options[options.index('--output-split-cfuncs') + 1] = '4000'
    isolated = mode.startswith('isolated')
    if isolated:
        options += ['+define+ISOLATED', '-CFLAGS', '-DISOLATED']
    if mode == 'protected':
        options += ['--protect-ids', '--protect-key', 'REPCUT_CONCURRENT']
    if mode == 'public':
        options += ['--public-flat-rw']
    if mode == 'trace':
        options += ['--trace']
    runtime = ['-fno-repcut']
    if not mode.endswith('stock'):
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
        for node in nodes:
            if node['kind'] not in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT'):
                continue
            label = node['label']
            owner = 0
            if any(name in label for name in ('right_state', 'guarded', 'memory')):
                owner = 1 % threads
            match = re.search(r'banks__BRA__(\d+)__KET__', label)
            if match:
                owner = int(match[1]) % threads
            pending = [int(node['id'])]
            while pending:
                ident = pending.pop()
                if ident not in parts[owner]:
                    parts[owner].add(ident)
                    pending.extend(dependencies[ident])
        membership = Path(test.obj_dir) / 'membership.csv'
        membership.write_text(''.join(','.join(map(str, sorted(p))) + ',\n' for p in parts),
                              encoding="utf8")
        runtime = ['--repcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=options + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    result = subprocess.run([str(Path(test.obj_dir).resolve() / test.vm_prefix)],
                            capture_output=True,
                            text=True,
                            timeout=60,
                            check=False)
    output = result.stdout + result.stderr
    (Path(test.obj_dir) / (mode + '.log')).write_text(output, encoding="utf8")
    assert result.returncode == 0, (mode, output)
    assert '*-* All Finished *-*' in output
    if mode.endswith('stock'):
        references[isolated] = output
    else:
        assert output == references[isolated], mode
        # RepCut must have actually partitioned this design. The reduced port no
        # longer batches kernels or locally publishes scalars, so only check the
        # partitioner ran; behavior is covered by the stock-equality check above.
        test.file_grep(test.stats, r'RepCut emit, functions\s+(\d+)')
        with base.with_suffix('.chunks.tsv').open(encoding="utf8") as stream:
            chunks = list(csv.DictReader(stream, delimiter='\t'))
        limit = 4000 if mode == 'packing' else 32
        assert chunks and all(int(row['body_nodes']) <= limit for row in chunks)
test.passes()
