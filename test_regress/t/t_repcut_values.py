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
    '-O3', '--stats', '--no-skip-identical', '--x-assign', '0', '--x-initial', '0',
    '--output-split-cfuncs', '64', '--output-split', '512', '-fno-split'
]
# Keep the table candidate and shared write groups together until RepCut lowering.
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')


def check_chain_trace(path):
    # Tracing alone must keep the original chain alive after its clocked
    # consumers move into partitions. Check every dumped value against inputs.
    scopes, signals, values = [], {}, {}
    samples = 0

    def check_sample():
        a, b = (values[signals['TOP.' + name]] for name in ('a', 'b'))
        link = ((a ^ b) + 1) & 0x7fffffff
        for n in range(16):
            if n:
                link = ((link << 1) ^ (link + a + n)) & 0x7fffffff
            name = f'TOP.t.chain[{n}].link_value'
            assert values[signals[name]] == link, (samples, name)

    timestamp = False
    for line in path.read_text(encoding="utf8").splitlines():
        words = line.split()
        if not words:
            continue
        if words[0] == '$scope':
            scopes.append(words[2])
        elif words[0] == '$upscope':
            scopes.pop()
        elif words[0] == '$var':
            signals['.'.join(scopes + [words[4]])] = words[3]
        elif words[0].startswith('#'):
            if timestamp:
                check_sample()
                samples += 1
            timestamp = True
        elif words[0][0] == 'b':
            if set(words[0][1:]) <= {'0', '1'}:
                values[words[1]] = int(words[0][1:], 2)
        elif words[0][0] in '01':
            values[words[0][1:]] = int(words[0][0])
    assert timestamp
    check_sample()
    assert samples + 1 == 2048, samples


for mode in ('stock', 'serial', 'parallel', 'protected', 'source_serial', 'source_parallel',
             'source_four', 'source_protected', 'source_trace_serial', 'source_trace_parallel',
             'source_vpi_serial', 'source_vpi_parallel'):
    threads = 4 if 'four' in mode else (1 if mode.endswith('serial') else 2)
    options = flags + (['--protect-ids', '--protect-key', 'REPCUT_VALUES']
                       if mode.endswith('protected') else [])
    options += ['-CFLAGS', '-DREPCUT_TEST_THREADS=' + str(threads)]
    source = mode.startswith('source_')
    trace = 'trace' in mode
    public = 'vpi' in mode
    if trace:
        options += ['--trace']
    if public:
        # Observe the chain without changing the initialization of input ports
        # used by the ROM test, as global --public-flat-rw would do.
        options += ['--vpi', '-DREPCUT_PUBLIC_CHAIN']
    if source:
        # Exercise source-body lowering as well as the table/imperative fallback.
        options += ['-fno-table']
    if mode == 'source_serial':
        options += ['--debug-self-test', '--debug-check']
    runtime = ['-fno-repcut']
    if mode != 'stock':
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=options + ['-fno-repcut', '--repcut-dump-graph'])
        assert 'complete 1' in base.with_suffix('.report.txt').read_text(encoding="utf8")
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        assert {'DIV', 'DIVS', 'MODDIV', 'MODDIVS'} <= {n['kind'] for n in nodes}
        dependencies = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [
            int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')
        ]
        for ordinal, sink in enumerate(sinks):
            part = parts[ordinal % threads]
            pending = [sink]
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
    stats = Path(test.stats).read_text(encoding="utf8")
    (Path(test.obj_dir) / (mode + '.stats')).write_text(stats, encoding="utf8")
    tables = re.search(r'Optimizations, Tables created\s+(\d+)', stats)
    assert (int(tables[1]) if tables else 0) == (0 if source else 1), mode
    if source:
        programs = re.search(r'RepCut native source, programs\s+(\d+)', stats)
        assert programs and int(programs[1]) == threads, mode
        guarded = re.search(r'RepCut native source, guarded scalar candidates\s+(\d+)', stats)
        assert guarded and int(guarded[1]) == (10 if threads == 1 else 8), mode
        groups = re.search(r'RepCut native source, scalar write groups\s+(\d+)', stats)
        assert groups and int(groups[1]) == {1: 2, 2: 2, 4: 4}[threads], mode
        # Unobserved chain computation belongs only in partition functions;
        # trace and public readers keep the native values alive.
        header = (Path(test.obj_dir) /
                  (test.vm_prefix + '___024root.h')).read_text(encoding="utf8")
        retained = bool(re.search(r'__DOT__chain.*__DOT__link_value', header))
        assert retained == (trace or public), mode
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    trace_path = Path(test.obj_dir).resolve() / (mode + '.vcd')
    test.execute(all_run_flags=[str(trace_path)] if trace else [])
    if trace:
        check_chain_trace(trace_path)
test.passes()
