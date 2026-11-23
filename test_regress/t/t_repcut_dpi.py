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
test.top_filename = str(Path(test.top_filename).resolve())
flags = [
    '--assert', '--threads-dpi', 'none', '--no-skip-identical', '--x-initial', '0', '--x-assign',
    '0', '--stats', '--output-split-cfuncs', '64', '--output-split', '512'
]
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
for mode in ('stock', 'native_serial', 'native_parallel', 'native_protected'):
    threads = 1 if mode in ('serial', 'native_serial') else 2
    options = flags + (['--protect-ids', '--protect-key', 'REPCUT_DPI']
                       if mode in ('protected', 'native_protected') else [])
    runtime = ['-fno-repcut']
    if mode != 'stock':
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=options + ['-fno-repcut', '--repcut-dump-graph'])
        assert 'complete 1' in base.with_suffix('.report.txt').read_text(encoding="utf8")
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        dependencies = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [
            int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'EFFECT', 'CALLBACK')
        ]
        captures = [n for n in nodes if n['kind'] == 'CALLBACK']
        assert len(captures) >= 2 and all(',' not in n['inputs'] for n in captures)
        assert any(n['kind'] == 'NEXT' for n in nodes)
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
        runtime = ['--repcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=options + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    if mode.startswith('native_'):
        test.file_grep(test.stats, r'RepCut native, callback procedures\s+(\d+)', 1)
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    result = subprocess.run([str(Path(test.obj_dir).resolve() / test.vm_prefix)],
                            capture_output=True,
                            text=True,
                            timeout=30,
                            check=True)
    output = result.stdout + result.stderr
    (Path(test.obj_dir) / (mode + '.log')).write_text(output, encoding="utf8")
    assert '*-* All Finished *-*' in output
    expected = [
        line.replace('EXPECT', 'ORDER', 1) for line in output.splitlines()
        if line.startswith('EXPECT')
    ]
    observed = [line for line in output.splitlines() if line.startswith('ORDER')]
    # Stock multithreaded Verilator buffers HDL displays until the worker
    # finishes, while DPI stdout is immediate. Compare each ordered stream.
    assert expected
    for calls in (False, True):
        want = [line for line in expected if line.startswith('ORDER call') == calls]
        got = [line for line in observed if line.startswith('ORDER call') == calls]
        assert want == got, (mode, calls,
                             next((i
                                   for i, pair in enumerate(zip(want, got)) if pair[0] != pair[1]),
                                  'length'))
test.passes()
