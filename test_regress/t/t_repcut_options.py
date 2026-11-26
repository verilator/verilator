#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json
import os
import shlex
import shutil
import subprocess
from pathlib import Path

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = 't/t_repcut_native.v'
directory = Path(test.obj_dir)
# The test reuses one build directory across many option combinations; start
# from a pristine one so a previous run's generated makefile cannot reference
# stale split files. (test.clean_objs() cannot be used here: its unquoted glob
# is broken by the "tools with space's" directory created below.)
if directory.exists():
    shutil.rmtree(directory)
directory.mkdir(parents=True)
base = directory / (test.vm_prefix + '__repcut_early')
tool_dir = directory / "tools with space's"
tool_dir.mkdir(exist_ok=True)
partitioner = tool_dir / 'rcp'
partitioner.write_text('''#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
p = argparse.ArgumentParser()
for key in ('graph_file', 'work_directory', 'nparts', 'threads', 'seed', 'target_ib'):
    p.add_argument('--' + key, required=True)
a = p.parse_args()
work = Path(a.work_directory)
with (work / 'invocations.jsonl').open('a') as f:
    f.write(json.dumps(vars(a)) + '\\n')
lines = Path(a.graph_file).read_text().splitlines()
count = int(lines[0].split()[1])
deps = [[] for _ in range(count)]
sinks = []
for node, line in enumerate(lines[1:]):
    outputs = [int(x) for x in line.split()[2:]]
    if not outputs:
        sinks.append(node)
    for output in outputs:
        deps[output].append(node)
parts = [set() for _ in range(int(a.nparts))]
for i, sink in enumerate(sinks):
    part = parts[i % len(parts)]
    pending = [sink]
    while pending:
        node = pending.pop()
        if node not in part:
            part.add(node)
            pending.extend(deps[node])
(work / 'rcp_output.txt').write_text(''.join(
    ','.join(map(str, sorted(part))) + '\\n' for part in parts))
''',
                       encoding="utf8")
partitioner.chmod(0o755)
driver = directory / 'driver.cpp'
driver.write_text(Path('t/t_repcut_native.cpp').read_text(encoding="utf8").replace(
    'Vt_repcut_native', test.vm_prefix),
                  encoding="utf8")
flags = [
    '--no-skip-identical', '--x-initial', '0', '--x-assign', '0', '--exe',
    str(driver.resolve())
]
stock_code = {}
repcut_code = {}
reference = None
saved_path = os.environ['PATH']
calls = Path(str(base) + '.partition') / 'invocations.jsonl'
calls.unlink(missing_ok=True)
os.environ['PATH'] = str(tool_dir.resolve()) + os.pathsep + saved_path
try:
    for threads in (1, 2):
        for case in ('stock', 'dormant', 'default', 'enabled', 'override', 'reenable',
                     'seed_default', 'diagnostics'):
            # Remove only generated model sources so stale split files cannot
            # affect the equality check or the next model build.
            for pattern in (test.vm_prefix + '*.cpp', test.vm_prefix + '*.h'):
                for path in directory.glob(pattern):
                    path.unlink()
            # Check diagnostic defaults in a clean artifact set, including when
            # reusing a directory after an explicit diagnostic invocation.
            for pattern in ('*.tsv', '*.report.txt'):
                for path in directory.glob(pattern):
                    path.unlink()
            for suffix in ('.graph', '.partial', '.partition.log'):
                Path(str(base) + suffix).unlink(missing_ok=True)
            shutil.rmtree(Path(str(base) + '.partition'), ignore_errors=True)
            extra = []
            if case == 'stock':
                extra = ['-fno-repcut']
            elif case == 'dormant':
                extra = ['-fno-repcut', '--repcut-partitioner', 'missing-partitioner']
            elif case == 'diagnostics':
                extra = ['--repcut-dump-graph']
            elif case == 'seed_default':
                extra = ['--repcut-seed', '42']
            elif case == 'enabled':
                extra = ['-frepcut']
            elif case == 'override':
                extra = ['-frepcut', '-fno-repcut', '--repcut-partitioner', 'missing-partitioner']
            elif case == 'reenable':
                extra = ['-fno-repcut', '-frepcut']
            enabled = case in ('default', 'enabled', 'reenable', 'seed_default', 'diagnostics')
            test.compile(make_main=False, threads=threads, verilator_flags2=flags + extra)
            assert test.repcut == enabled, (threads, case)
            tables = list(directory.glob('*.tsv'))
            reports = list(directory.glob('*.report.txt'))
            if case == 'diagnostics':
                expected = ('.nodes.tsv', '.storage.tsv', '.domains.tsv', '.bindings.tsv',
                            '.regions.tsv', '.controls.tsv', '.memories.tsv', '.clocks.tsv',
                            '.plan.tsv', '.owners.tsv', '.chunks.tsv', '.cuts.tsv',
                            '.publication.tsv', '.native-costs.tsv', '.report.txt')
                assert all(Path(str(base) + suffix).is_file() for suffix in expected)
                assert list(directory.glob('*.source-costs.tsv'))
            else:
                assert not tables and not reports, (threads, case, tables, reports)
            code = {
                p.name: p.read_bytes()
                for pattern in (test.vm_prefix + '*.cpp', test.vm_prefix + '*.h')
                for p in directory.glob(pattern)
            }
            if case == 'stock':
                stock_code[threads] = code
            if not enabled:
                assert code == stock_code[threads], (threads, case)
                assert not any(b'__Vrepcut' in data for data in code.values())
            else:
                if case == 'default':
                    repcut_code[threads] = code
                assert code == repcut_code[threads], (threads, case)
                assert any(b'__Vrepcut' in data for data in code.values())
                generated = Path(str(base) + '.partition') / 'rcp_output.txt'
                if case == 'diagnostics':
                    assert len(generated.read_text(encoding="utf8").splitlines()) == threads
                    assert Path(str(base) + '.graph').is_file()
                else:
                    assert not Path(str(base) + '.graph').exists()
                    assert not Path(str(base) + '.partition').exists()
                    assert not Path(str(base) + '.partition.log').exists()
            result = subprocess.run([str((directory / test.vm_prefix).resolve())],
                                    capture_output=True,
                                    text=True,
                                    timeout=30,
                                    check=True)
            if reference is None:
                reference = result.stdout
                assert '*-* All Finished *-*' in reference
            assert result.stdout == reference, (threads, case)
    # The linked path must not need a partition directory, even if that path
    # is occupied by an unrelated file.
    work = Path(str(base) + '.partition')
    shutil.rmtree(work)
    work.write_text('not a partition directory', encoding='utf8')
    test.compile(make_main=False, verilator_make_gmake=False, threads=2, verilator_flags2=flags)
    assert work.read_text(encoding='utf8') == 'not a partition directory'
    work.unlink()
    # A tool named rcp on PATH must not intercept the bundled default.
    assert not calls.exists(), 'Default partitioning invoked an external executable'
    for seed in (0, 7, 42, 2147483647):
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=2,
                     verilator_flags2=flags + [
                         '--repcut-partitioner',
                         shlex.quote(str(partitioner.resolve())), '--repcut-seed',
                         str(seed)
                     ])
    invocations = [json.loads(line) for line in calls.read_text(encoding="utf8").splitlines()]
    assert [int(call['seed']) for call in invocations] == [0, 7, 42, 2147483647]
    for invocation in invocations:
        assert invocation['nparts'] == '2'
        assert invocation['threads'] == '1'
        assert invocation['target_ib'] == '0.03'
    # Exercise a nondefault seed through the linked API and replay it in a fresh
    # compiler process. A valid different seed need not select a different cut.
    replay = None
    for _ in range(2):
        test.compile(make_main=False,
                     threads=2,
                     verilator_flags2=flags + ['--repcut-seed', '7', '--repcut-dump-graph'])
        membership = Path(str(base) + '.partition') / 'rcp_output.txt'
        current = membership.read_bytes()
        if replay is not None:
            assert current == replay
        replay = current
        test.file_grep(str(base) + '.partition.log', r'Bundled RepCut: seed 7,')
        result = subprocess.run([str((directory / test.vm_prefix).resolve())],
                                capture_output=True,
                                text=True,
                                timeout=30,
                                check=True)
        assert result.stdout == reference
    # Tiny and empty graphs must preserve idle worker slots without invoking an
    # external hypergraph partitioner on an edgeless partitioning problem.
    trivial = directory / 'trivial.v'
    for rtl in ('module t; endmodule\n', ('module t(input logic clk, d, output logic q); '
                                          'always @(posedge clk) q <= d; endmodule\n')):
        trivial.write_text(rtl, encoding="utf8")
        test.top_filename = str(trivial.resolve())
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=4,
                     verilator_flags2=[
                         '-frepcut', '--repcut-partitioner', 'missing-partitioner',
                         '--no-skip-identical'
                     ])
        generated = Path(str(base) + '.partition') / 'rcp_output.txt'
        assert len(generated.read_text(encoding="utf8").splitlines()) == 4
    test.top_filename = 't/t_repcut_native.v'
    for mode in ('lint-only', 'dpi-hdr-only', 'json-only'):
        output = directory / mode
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=2,
                     verilator_flags2=[
                         '--' + mode, '--Mdir',
                         str(output), '-frepcut', '--repcut-partitioner', 'missing-partitioner',
                         '--no-skip-identical'
                     ])
        assert not list(output.glob('*__repcut*')), mode
finally:
    os.environ['PATH'] = saved_path

test.passes()
