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
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
for case, threads in [('stock', 1), ('serial', 1), ('parallel', 2), ('fallback', 2),
                      ('save_serial', 1), ('save_parallel', 2)]:
    flags = [
        '--stats', '--no-skip-identical', '-fno-table', '-CFLAGS',
        f'-DREPCUT_TEST_THREADS={threads}'
    ]
    if case == 'fallback':
        flags += ['--output-split-cfuncs', '64']
    if case == 'serial':
        flags += ['--debug-self-test', '--debug-check']
    if case.startswith('save_'):
        flags += ['--savable', '-CFLAGS', '-DDECODER_SAVE']
    runtime = ['-fno-repcut']
    if case != 'stock':
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        dependencies = [[int(x) for x in node['inputs'].split(',') if x] for node in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [int(node['id']) for node in nodes if node['kind'] in ('NEXT', 'OUTPUT')]
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
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    if case != 'stock':
        stats = Path(test.stats).read_text(encoding="utf8")
        stats_path = Path(test.obj_dir) / (case + '.stats')
        stats_path.write_text(stats, encoding="utf8")
        test.file_grep(stats_path, r'Optimizations, DFG, BinToOneHot, decoders created\s+(\d+)', 2)
        if case == 'fallback':
            count = re.search(r'RepCut native source, (?:graph fallback|hybrid) programs\s+(\d+)',
                              stats)
            assert count and int(count[1]) > 0
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    result = subprocess.run([
        str(Path(test.obj_dir).resolve() / test.vm_prefix),
        str(Path(test.obj_dir).resolve() / (case + '.save'))
    ],
                            capture_output=True,
                            text=True,
                            timeout=60,
                            check=False)
    (Path(test.obj_dir) / (case + '.log')).write_text(result.stdout + result.stderr,
                                                      encoding="utf8")
    result.check_returncode()
    assert '*-* All Finished *-*' in result.stdout
test.passes()
