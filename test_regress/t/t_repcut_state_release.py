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
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
cases = [('stock', 1, [], 0), ('serial', 1, [], 0), ('self_test', 1, ['--debug-self-test'], 0),
         ('parallel', 2, [], 0), ('protected', 1, ['--protect-ids'], 0),
         ('trace', 1, ['--trace'], 0), ('vpi', 1, ['--vpi'], 0),
         ('coverage', 1, ['--coverage'], 0), ('public', 1, ['+define+PUBLIC_STATE'], 0),
         ('observer', 1, ['+define+EXTRA_OBSERVER', '--timing'], 1),
         ('comb_observer', 1, ['+define+COMB_OBSERVER'], 3),
         ('two_clocks', 1, ['+define+SECOND_CLOCK'], 2)]
cases += [('decoder_stock', 1, [], 0), ('decoder', 1, [], 0),
          ('decoder_protected', 1, ['--protect-ids'], 0), ('decoder_parallel', 2, [], 0),
          ('decoder_observer', 1, ['+define+EXTRA_OBSERVER', '--timing'], 1),
          ('decoder_comb_observer', 1, ['+define+COMB_OBSERVER'], 3),
          ('decoder_two_clocks', 1, ['+define+SECOND_CLOCK'], 2),
          ('decoder_unused_import', 1, ['+define+FOREIGN_IMPORT'], 0),
          ('decoder_foreign', 1, ['+define+FOREIGN_IMPORT', '+define+FOREIGN_OBSERVER'], 4),
          ('decoder_user_table', 1, ['+define+USER_TABLE'], 5),
          ('decoder_dump', 1, ['--dump-tree', '--dump-tree-json'], 0)]
for case, threads, extra, observer in cases:
    decoder = case.startswith('decoder')
    if decoder:
        extra = extra + ['+define+DECODER_STATE', '-CFLAGS', '-DREPCUT_TEST_DECODER']
    flags = [
        '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0', '-fno-table',
        '--output-split-cfuncs', '64', '--output-split', '512', '-CFLAGS',
        f'-DREPCUT_TEST_THREADS={threads}', '-CFLAGS', f'-DREPCUT_TEST_OBSERVER={observer}'
    ] + extra
    runtime = ['-fno-repcut']
    if case not in ('stock', 'decoder_stock'):
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
        for ordinal, node in enumerate(nodes):
            if node['kind'] not in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT'):
                continue
            pending = [int(node['id'])]
            while pending:
                index = pending.pop()
                part = parts[ordinal % threads]
                if index not in part:
                    part.add(index)
                    pending.extend(deps[index])
        assert set().union(*parts) == set(range(len(nodes)))
        membership = Path(test.obj_dir) / 'membership.csv'
        membership.write_text(''.join(','.join(map(str, sorted(p))) + '\n' for p in parts),
                              encoding="utf8")
        runtime = ['--repcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    stats = Path(test.stats).read_text(encoding="utf8")
    stats_path = Path(test.obj_dir) / (case + '.stats')
    stats_path.write_text(stats, encoding="utf8")
    if case not in ('stock', 'decoder_stock'):
        count = re.search(r'RepCut native, directly updated scalars\s+(\d+)', stats)
        assert count, case
        if case in ('serial', 'self_test', 'protected'):
            # Compiler self-tests must not introduce observers into the model.
            assert int(count[1]) == 3, (case, 'Unexpected guarded-state release count')
        elif case in ('decoder', 'decoder_protected', 'decoder_unused_import', 'decoder_dump'):
            # This exact count is checked after the new decoder observer proof.
            assert int(count[1]) == 4, (case, 'Decoder blocked guarded-state release')
            test.file_grep(stats_path,
                           r'RepCut native direct-state, retained decoders allowed\s+(\d+)', 1)
        else:
            assert int(count[1]) == 0, (case, 'Observer boundary was ignored')
        if case == 'decoder_user_table':
            test.file_grep(stats_path,
                           r'RepCut native direct-state, rejected retained observer\s+1')
        # Report independent restrictions even when a prior guard already
        # excludes the model. Keep the behavioral release checks above.
        restriction = {
            'parallel': 'threads',
            'coverage': 'coverage',
            'trace': 'tracing',
            'vpi': 'VPI',
            'observer': 'lifecycle or callable block',
            'two_clocks': 'domains',
            'decoder_user_table': 'retained procedures'
        }.get(case)
        if restriction:
            test.file_grep(stats_path,
                           r'RepCut native direct-state, blocked ' + restriction + r'\s+(\d+)', 1)
        if case == 'decoder_dump':
            assert any('[DFGDEC]' in Path(p).read_text(encoding="utf8")
                       for p in test.glob_some(test.obj_dir + '/*.tree'))
            assert any(
                re.search(r'"isDfgDecoder"\s*:\s*true',
                          Path(p).read_text(encoding="utf8"))
                for p in test.glob_some(test.obj_dir + '/*.tree.json'))
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    result = subprocess.run([
        str(Path(test.obj_dir).resolve() / test.vm_prefix),
        str(Path(test.obj_dir).resolve() / (case + '.vcd'))
    ],
                            capture_output=True,
                            text=True,
                            timeout=30,
                            check=False)
    output = result.stdout + result.stderr
    (Path(test.obj_dir) / (case + '.log')).write_text(output, encoding="utf8")
    result.check_returncode()
    assert '*-* All Finished *-*' in output, (case, output)
test.passes()
