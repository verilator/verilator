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
    '--output-split-cfuncs', '64', '--output-split', '512'
]
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
references = {}
for case in ('stock', 'stock_vpi', 'serial', 'parallel', 'protected', 'trace', 'vpi',
             'stock_features', 'features_serial', 'features_parallel', 'stock_cycle',
             'cycle_serial', 'cycle_parallel', 'stock_save', 'save_serial', 'save_parallel',
             'stock_coverage', 'coverage', 'profile', 'profile_use'):
    mode = case
    # Use a serial stock oracle: stock MTasks with timing and context DPI can
    # produce different trajectories across runs of the same executable.
    # RepCut's parallel variants must still match the complete serial trajectory.
    threads = 1 if mode.startswith('stock') or mode.endswith('serial') else 2
    options = (['--trace'] if mode == 'trace' else []) + flags + (
        ['--protect-ids', '--protect-key', 'REPCUT_NATIVE'] if mode == 'protected' else [])
    runtime = ['-fno-repcut']
    if mode == 'serial':
        options += [
            '--debug-self-test', '--debug-check', '--dumpi-tree', '3', '--dumpi-tree-json', '3'
        ]
    features = 'features' in mode
    cycle = 'cycle' in mode
    comparison = (features, cycle)
    if features:
        options += ['--timing', '-DNATIVE_FEATURES', '-CFLAGS', '-DNATIVE_FEATURES']
    if cycle:
        # Keep feedback present at the post-optimization extraction boundary.
        options += ['-DNATIVE_CYCLE', '-Wno-UNOPTFLAT']
    if 'save' in mode:
        options += ['--savable', '-CFLAGS', '-DNATIVE_SAVE']
    if 'coverage' in mode:
        options += ['--coverage']
    profile = (Path(test.obj_dir) / 'profile.vlt').resolve()
    if mode == 'profile':
        options += ['--prof-pgo']
    if mode == 'profile_use':
        options += [str(profile)]
    if mode in ('stock_vpi', 'vpi'):
        options += ['--vpi', '--public-flat-rw']
    if not mode.startswith('stock') and mode != 'profile_use':
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=options + ['-fno-repcut', '--repcut-dump-graph'])
        report = base.with_suffix('.report.txt').read_text(encoding="utf8")
        (Path(test.obj_dir) / (case + '.report.txt')).write_text(report, encoding="utf8")
        assert 'complete 1' in report
        if features:
            assert 'native_retained ' in report
        # Master always runs DFG breakCycles before RepCut extraction, so a combinational
        # cycle cannot survive to this boundary; native_cycle_boundaries is always 0 here.
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        dependencies = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [
            int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')
        ]
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
    if not mode.startswith('stock'):
        # PGO changes costs after partitioning; return the same membership.
        runtime = ['-frepcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=options + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    if not mode.startswith('stock'):
        stats = Path(test.stats).read_text(encoding="utf8")
        (Path(test.obj_dir) / (case + '.stats')).write_text(stats, encoding="utf8")
        count = re.search(r'RepCut native, replaced procedures\s+(\d+)', stats)
        expected_procedures = 7 if features else (5 if mode == 'coverage' else 6)
        assert count and int(count[1]) == expected_procedures, mode
        count = re.search(r'RepCut native source, programs\s+(\d+)', stats)
        assert count and int(count[1]) == threads * (6 if features else 5), mode
        assert 'RepCut native source, graph fallback programs' not in stats, mode
        # The scheduler must see the kernel's reads and writes, but unused
        # dependency parameters must not survive into the C++ runtime ABI.
        for filename in test.glob_some(test.obj_dir + '/*.cpp'):
            assert '__Vdependency' not in Path(filename).read_text(encoding="utf8"), (mode,
                                                                                      filename)
        count = re.search(r'RepCut native, dependency operands removed\s+(\d+)', stats)
        # Master breaks combinational cycles before extraction, so cycle modes now match
        # ordinary modes here.
        expected_operands = 32 if features else (28 if mode == 'vpi' else 30)
        batch = re.search(r'RepCut native batch, domains\s+(\d+)', stats)
        if batch:
            assert int(batch[1]) == (6 if features else 5), case
            # Batched compute and retained publication processes carry completion dependencies.
            expected_operands += 1 + expected_procedures
        assert count and int(count[1]) == expected_operands, case
        assert 'RepCut native publication, dispatches' not in stats, case
        if mode == 'serial':
            # Exercise the dependency marker's tree and JSON dumps before its
            # removal, and verify the final lowering clears it from the AST.
            trees = test.glob_some(test.obj_dir + '/*_repcut_dependencies.tree')
            assert all('[REPCUTDEPS]' not in Path(p).read_text(encoding="utf8") for p in trees)
            dumps = test.glob_some(test.obj_dir + '/*_*.tree.json')
            assert any(
                re.search(r'"repcutDependencyArgs":\s*true',
                          Path(p).read_text(encoding="utf8")) for p in dumps)
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    run_flags = ['+verilator+prof+vlt+file+' + str(profile)] if mode == 'profile' else []
    result = subprocess.run([
        str(Path(test.obj_dir).resolve() / test.vm_prefix),
        str(Path(test.obj_dir).resolve() / (case + '.vcd'))
    ] + run_flags,
                            capture_output=True,
                            text=True,
                            timeout=30,
                            check=False)
    output = result.stdout + result.stderr
    (Path(test.obj_dir) / (case + '.log')).write_text(output, encoding="utf8")
    result.check_returncode()
    assert '*-* All Finished *-*' in output
    if comparison not in references:
        references[comparison] = output
    else:
        assert output == references[comparison], mode
    if mode == 'trace':
        assert (Path(test.obj_dir) / (case + '.vcd')).stat().st_size > 1000
    if mode == 'profile':
        costs = re.findall(
            r'profile_data -model "' + test.vm_prefix + r'" -mtask "[^"]+" -cost 64\'d(\d+)',
            profile.read_text(encoding="utf8"))
        assert costs and all(0 < int(cost) < 10**18 for cost in costs)
    if mode == 'profile_use':
        test.file_grep_not(test.compile_log_filename, r'PROFOUTOFDATE')
    if mode == 'coverage':

        def points(name):
            rows = (Path(test.obj_dir) / (name + '.vcd')).read_text(encoding="utf8").splitlines()
            counts = {
                row.rsplit(' ', 1)[0]: int(row.rsplit(' ', 1)[1])
                for row in rows if row.startswith('C ')
            }
            assert counts and any(counts.values())
            return counts

        assert points(case) == points('stock_coverage')
test.passes()
