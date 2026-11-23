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
membership = Path(test.obj_dir) / 'membership.csv'
for fmt in ('vcd', 'fst'):
    for case, threads, split, words in (('stock_small', 2, 64, 1), ('small', 2, 64, 1),
                                        ('stock', 2, 64, 512), ('parallel', 2, 64, 512),
                                        ('four', 4, 64, 512), ('unsplit', 2, 0, 512)):
        reference = str(
            Path(test.obj_dir).resolve() / (('stock_small.' if words == 1 else 'stock.') + fmt))
        flags = [
            '--trace-' + fmt, '--trace-structs', '--stats', '--no-skip-identical', '--debug-check',
            '--x-initial', '0', '--x-assign', '0', '--output-split-cfuncs',
            str(split), f'-GSTATE_WORDS={words}', '-CFLAGS', f'-DREPCUT_STATE_WORDS={words}'
        ]
        runtime = ['-fno-repcut']
        if not case.startswith('stock'):
            test.compile(make_main=False,
                         verilator_make_gmake=False,
                         threads=threads,
                         verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
            assert 'complete 1\n' in base.with_suffix('.report.txt').read_text(encoding="utf8")
            with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
                nodes = list(csv.DictReader(stream, delimiter='\t'))
            deps = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
            with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
                for row in csv.DictReader(stream, delimiter='\t'):
                    deps[int(row['node'])].append(int(row['predicate']))
            parts = [set() for _ in range(threads)]
            sinks = [
                int(n['id']) for n in nodes
                if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')
            ]
            for ordinal, sink in enumerate(sinks):
                pending = [sink]
                part = parts[ordinal % threads]
                while pending:
                    node = pending.pop()
                    if node not in part:
                        part.add(node)
                        pending.extend(deps[node])
            assert set().union(*parts) == set(range(len(nodes)))
            membership.write_text(''.join(','.join(map(str, sorted(p))) + '\n' for p in parts),
                                  encoding="utf8")
            runtime = ['--repcut', '--repcut-partitioner', partitioner(test, membership)]
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + runtime +
                     ['--exe', str(Path(test.pli_filename).resolve())])
        stats = Path(test.stats).read_text(encoding="utf8")
        # file_grep caches contents, so use a fresh filename for every build.
        stats_path = Path(test.obj_dir) / (case + '-' + fmt + '.stats')
        stats_path.write_text(stats, encoding="utf8")
        if not case.startswith('stock') and words > 1:
            test.file_grep(str(stats_path), r'RepCut native publication, dispatches\s+(\d+)', 2)
            test.file_grep(str(stats_path), r'RepCut native publication, parallel scalars\s+(\d+)',
                           65)
        elif case == 'small':
            assert 'RepCut native publication, dispatches' not in stats
        trace_check = Path(test.obj_dir) / (case + '-' + fmt + '.trace.txt')
        trace_check.write_text(''.join(
            Path(path).read_text(encoding="utf8")
            for path in test.glob_some(test.obj_dir + '/' + test.vm_prefix +
                                       '__RtmdHierTable*.cpp')),
                               encoding="utf8")
        # Tracing now reads runtime model descriptors, including structured state.
        # The traced values remain identical across publication modes (below).
        test.file_grep(str(trace_check), r'structured_state')
        # Keep a real conditional trace path: always-tracing would mask a missing
        # caller activity edge even if the register oracle still passes.
        assert re.search(r'Tracing, Activity setters fast\s+[1-9]\d*', stats), case
        subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'],
                       check=True)
        trace = str(Path(test.obj_dir).resolve() / (case + '.' + fmt))
        result = subprocess.run(
            [str(Path(test.obj_dir).resolve() / test.vm_prefix), trace,
             str(threads)],
            capture_output=True,
            text=True,
            timeout=30,
            check=False)
        output = result.stdout + result.stderr
        (Path(test.obj_dir) / (case + '-' + fmt + '.log')).write_text(output, encoding="utf8")
        result.check_returncode()
        assert '*-* All Finished *-*' in output
        if not case.startswith('stock'):
            test.trace_identical(trace, reference)
test.passes()
