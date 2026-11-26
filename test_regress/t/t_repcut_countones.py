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
                             ('four', 4, []), ('source', 2, ['-fno-dfg']),
                             ('protected', 2, ['--protect-ids'])]:
    flags = [
        '--assert', '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0',
        '-fno-table', '--output-split-cfuncs', '64', '-CFLAGS', f'-DREPCUT_TEST_THREADS={threads}'
    ] + extra
    runtime = ['-fno-repcut']
    if case != 'stock':
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
        report = base.with_suffix('.report.txt').read_text(encoding="utf8")
        assert 'complete 1\n' in report, case
        assert 'native_retained' not in report, (case, report)
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        counts = [n for n in nodes if n['kind'] == 'COUNTONES']
        assert counts, (case, 'Population count missing from partition graph')
        deps = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                deps[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        for ordinal, n in enumerate(nodes):
            if n['kind'] not in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT'):
                continue
            pending = [int(n['id'])]
            while pending:
                node = pending.pop()
                part = parts[ordinal % threads]
                if node not in part:
                    part.add(node)
                    pending.extend(deps[node])
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
    (Path(test.obj_dir) / (case + '.stats')).write_text(Path(
        test.stats).read_text(encoding="utf8"),
                                                        encoding="utf8")
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    test.execute()
test.passes()
