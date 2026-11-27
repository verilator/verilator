#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
import subprocess
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
for case, threads, extra in [('stock', 1, []), ('serial', 1, []), ('parallel', 2, []),
                             ('parallel4', 4, []), ('protected', 2, ['--protect-ids']),
                             ('source', 2, ['-fno-dfg']), ('public', 2, ['--public-flat-rw'])]:
    flags = [
        '--assert', '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0',
        '--threads-dpi', 'none', '--output-split-cfuncs', '64', '-CFLAGS',
        f'-DREPCUT_TEST_THREADS={threads}'
    ] + extra
    runtime = ['-fno-repcut']
    if case != 'stock':
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
        assert 'complete 1\n' in base.with_suffix('.report.txt').read_text(encoding="utf8")
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        deps = [[int(x) for x in node['inputs'].split(',') if x] for node in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                deps[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        for ordinal, node in enumerate(nodes):
            if node['kind'] not in ('NEXT', 'OUTPUT', 'CALLBACK'):
                continue
            pending = [int(node['id'])]
            part = parts[ordinal % threads]
            while pending:
                current = pending.pop()
                if current not in part:
                    part.add(current)
                    pending.extend(deps[current])
        assert set().union(*parts) == set(range(len(nodes)))
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
        stats_path = Path(test.obj_dir) / (case + '.stats')
        stats_path.write_text(Path(test.stats).read_text(encoding="utf8"), encoding="utf8")
        test.file_grep(str(stats_path), r'RepCut native, callback procedures\s+(\d+)', 3)
        # Native kernel batching (and its staged/concurrent variants) is not part of the
        # reduced master port, so those statistics are not checked here.
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    test.execute()
test.passes()
