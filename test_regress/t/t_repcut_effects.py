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
import shlex
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
for mode in ('stock', 'serial', 'parallel', 'protected', 'stock_coverage', 'coverage',
             'stock_multi', 'multi_serial', 'multi_parallel', 'stock_fallback', 'fallback_serial',
             'fallback_parallel'):
    # Stock MT defers console displays but writes file descriptors directly;
    # use its serial execution as the ordered-output reference.
    threads = 1 if mode.startswith('stock') or mode.endswith('serial') else 2
    options = flags + (['--protect-ids', '--protect-key', 'REPCUT_EFFECTS']
                       if mode == 'protected' else [])
    runtime = ['-fno-repcut']
    if 'multi' in mode:
        options += ['-DREPCUT_EFFECT_MULTI', '-CFLAGS', '-DREPCUT_EFFECT_MULTI']
    if 'fallback' in mode:
        options += [
            '-DREPCUT_EFFECT_FALLBACK', '-CFLAGS', '-DREPCUT_EFFECT_FALLBACK',
            '--output-split-cfuncs', '32', '-fno-dfg'
        ]
    effect_count = 8 if 'multi' in mode or 'fallback' in mode else 7
    if 'coverage' in mode:
        options += ['--coverage']
    if not mode.startswith('stock'):
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
        sinks = [int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'EFFECT')]
        assert sum(n['kind'] == 'EFFECT' for n in nodes) == effect_count
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
        runtime = ['-frepcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=options + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    if not mode.startswith('stock'):
        stats = Path(test.stats).read_text(encoding="utf8")
        captured = re.search(r'RepCut native, captured effects\s+(\d+)', stats)
        assert captured and int(captured[1]) == effect_count, mode
        pending = re.search(r'RepCut native, effect pending flags\s+(\d+)', stats)
        scans = re.search(r'RepCut native, guarded effect scans\s+(\d+)', stats)
        expected_pending = threads + int('multi' in mode)
        assert pending and int(pending[1]) == expected_pending, mode
        assert scans and int(scans[1]) == (2 if 'multi' in mode else 1), mode
        if 'fallback' in mode:
            fallback = re.search(
                r'RepCut native source, (?:graph fallback|hybrid) programs\s+(\d+)', stats)
            assert fallback and int(fallback[1]) > 0, mode
        manifest = Path(test.obj_dir) / (test.vm_prefix + '__verFiles.dat')
        generated = [
            Path(shlex.split(line)[-1])
            for line in manifest.read_text(encoding="utf8").splitlines()
            if line.startswith('T ') and line.endswith('.cpp"')
        ]
        assert generated
        if mode in ('serial', 'parallel', 'multi_serial', 'multi_parallel'):
            # Capturing a display must retain the source's cold-branch hint,
            # including nested guards and arms outlined by the small CFunc limit.
            # Match the real enable test, not the input-width debug assertion.
            code = '\n'.join(path.read_text(encoding="utf8") for path in generated)
            # Shared helpers can leave these bodies as C++ member functions, and
            # master groups top-level ports into a struct.
            receiver = r'(?:vlSelfRef\.(?:__VprimaryPorts\.)?|this->(?:__VprimaryPorts\.)?)'
            assert re.search(r'if \(VL_UNLIKELY\(\(' + receiver + r'enable\)\)\)', code), mode
            assert re.search(
                r'if \(VL_UNLIKELY\(\(+1U & \((?:::)?IData\)\(' + receiver + r'data\)', code), mode
        if mode != 'coverage':
            # These wires have no native consumer after their predicates and
            # arguments move into partitions; do not recompute their cone.
            for path in generated:
                assert '__DOT__effect_chain' not in path.read_text(encoding="utf8"), (mode, path)
    # Check that the aggregate clears on disabled edges, even though stale
    # aggregate flags alone would only waste time and leave output unchanged.
    check = 'return true;'
    includes = ''
    if mode != 'protected' and 'multi' not in mode \
            and not mode.startswith('stock'):
        references = set()
        for path in generated:
            references.update(
                re.findall(r'vlSelfRef\.([\w.]*__Vrepcut_native0_p\d+_effect_pending)',
                           path.read_text(encoding="utf8")))
        assert len(references) == threads, (mode, references)
        pending = ' | '.join('model.rootp->' + name for name in sorted(references))
        includes = '#include "' + test.vm_prefix + '___024root.h"\n'
        check = ('return !model.clk || model.bad || model.done || '
                 'bool(' + pending + ') == bool(model.enable);')
    (Path(test.obj_dir) / 'repcut_effect_pending.h').write_text(
        includes + 'static bool checkEffectPending(const ' + test.vm_prefix +
        '& model) { (void)model; ' + check + ' }\n',
        encoding="utf8")
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    for finish in (False, True):
        coverage = Path(test.obj_dir).resolve() / (mode +
                                                   ('-finish' if finish else '-assert') + '.dat')
        arguments = ['+finish' if finish else '+assert']
        if 'coverage' in mode:
            arguments += [str(coverage)]
        result = subprocess.run([str(Path(test.obj_dir).resolve() / test.vm_prefix)] + arguments,
                                capture_output=True,
                                text=True,
                                timeout=30,
                                check=True)
        output = result.stdout + result.stderr
        (Path(test.obj_dir) / (mode + ('-finish' if finish else '-assert') + '.log')).write_text(
            output, encoding="utf8")
        assert '*-* All Finished *-*' in output
        expected = [
            line.replace('EXPECT', 'EFFECT', 1) for line in output.splitlines()
            if line.startswith('EXPECT')
        ]
        observed = [line for line in output.splitlines() if line.startswith('EFFECT')]
        assert expected and expected == observed, (mode, finish, expected, observed)
        assert output.count('EXPECTED ASSERTION FAILURE') == int(not finish)
        if mode == 'coverage':

            def points(path):
                counts = {
                    row.rsplit(' ', 1)[0]: int(row.rsplit(' ', 1)[1])
                    for row in path.read_text(encoding="utf8").splitlines() if row.startswith('C ')
                }
                assert counts and any(counts.values())
                return counts

            assert points(coverage) == points(coverage.with_name('stock_' + coverage.name))
test.passes()
