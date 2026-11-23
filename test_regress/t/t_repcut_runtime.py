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
test.top_filename = str(Path('t/t_repcut_runtime.v').resolve())
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
variants = [(2, False, False, False, 'split'), (2, True, False, False, 'split'),
            (2, False, True, False, 'split'), (2, False, False, True, 'split'),
            (2, True, False, True, 'split'), (2, False, False, False, 'main'),
            (2, False, False, False, 'worker')]
variants += [(1, negative, False, initial_edge, 'split') for negative in (False, True)
             for initial_edge in (False, True)]
for threads, negative, protect, initial_edge, placement in variants:
    flags = ['--no-skip-identical', '--output-split-cfuncs', '32', '--output-split', '256']
    if initial_edge:
        flags += ['--x-initial-edge']
    if protect:
        flags += ['--protect-ids', '--protect-key', 'REPCUT_RUNTIME_TEST']
    if negative:
        flags += ['+define+REPCUT_NEGEDGE']
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
    with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
        nodes = list(csv.DictReader(stream, delimiter='\t'))
    for node in nodes:
        node['inputs'] = [int(i) for i in node['inputs'].split(',') if i]
        node['dependencies'] = node['inputs'].copy()
    with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
        for control in csv.DictReader(stream, delimiter='\t'):
            nodes[int(control['node'])]['dependencies'].append(int(control['predicate']))
    part_count = threads
    parts = [set() for _ in range(part_count)]
    sinks = [i for i, node in enumerate(nodes) if node['kind'] in ('NEXT', 'OUTPUT')]
    for ordinal, sink in enumerate(sinks):
        owner = ordinal % part_count if placement == 'split' else int(placement == 'worker')
        pending = [sink]
        while pending:
            i = pending.pop()
            if i not in parts[owner]:
                parts[owner].add(i)
                pending.extend(nodes[i]['dependencies'])
    membership = Path(test.obj_dir) / 'membership.csv'
    membership.write_text(''.join(','.join(map(str, sorted(p))) + (',\n' if p else '\n')
                                  for p in parts),
                          encoding="utf8")
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + [
                     '--repcut', '--repcut-partitioner',
                     partitioner(test, membership), '--exe',
                     str(Path(test.pli_filename).resolve()), '-CFLAGS', '-DREPCUT_NEGEDGE=' +
                     str(int(negative)), '-CFLAGS', '-DREPCUT_INITIAL_EDGE=' +
                     str(int(initial_edge)), '-CFLAGS', '-DVL_THREADS_SERIAL_COST=0'
                 ])
    subprocess.run(
        ['make', '-C',
         str(Path(test.obj_dir).resolve()), '-f', test.vm_prefix + '.mk', '-j2'],
        check=True)
    test.execute()
    for pch in Path(test.obj_dir).glob(test.vm_prefix + '__pch.h.*.gch'):
        pch.unlink()
test.passes()
