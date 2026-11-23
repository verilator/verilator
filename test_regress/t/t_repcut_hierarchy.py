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
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vlt_all')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = 't/t_hier_block_struct.v'
threads = 2 if test.vltmt else 1
config = (Path(test.obj_dir) / 'workers.vlt').resolve()
config.write_text('`verilator_config\nhier_workers -module "Test" -workers ' + str(threads) + '\n',
                  encoding="utf8")
flags = ['--hierarchical', '--stats', '--no-skip-identical', '-Wno-UNOPTFLAT', str(config)]

test.compile(threads=threads,
             verilator_make_gmake=False,
             verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])

plans = (Path(test.obj_dir) / 'partitions').resolve()
plans.mkdir(exist_ok=True)
models = {}
for table in sorted(Path(test.obj_dir).rglob('*__repcut_early.nodes.tsv')):
    prefix = table.name.removesuffix('__repcut_early.nodes.tsv')
    base = table.with_name(prefix + '__repcut_early')
    report = base.with_suffix('.report.txt').read_text(encoding="utf8")
    assert 'complete 1\n' in report, prefix
    count = int(re.search(r'^native_threads (\d+)$', report, re.MULTILINE)[1])
    # Master assigns per-block workers; a circular/inout child may get fewer than the
    # top-level thread count, so accept any count up to the configured threads.
    assert 1 <= count <= threads, (prefix, count)
    with table.open(encoding="utf8") as stream:
        nodes = list(csv.DictReader(stream, delimiter='\t'))
    deps = [[int(x) for x in node['inputs'].split(',') if x] for node in nodes]
    with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            deps[int(row['node'])].append(int(row['predicate']))
    parts = [set() for _ in range(count)]
    sinks = [
        int(node['id']) for node in nodes
        if node['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT', 'CALLBACK')
    ]
    for ordinal, sink in enumerate(sinks):
        part = parts[ordinal % count]
        pending = [sink]
        while pending:
            node = pending.pop()
            if node not in part:
                part.add(node)
                pending.extend(deps[node])
    assert set().union(*parts) == set(range(len(nodes))), prefix
    (plans / (prefix + '.csv')).write_text(''.join(','.join(map(str, sorted(part))) + '\n'
                                                   for part in parts),
                                           encoding="utf8")
    models[prefix] = count
# Master may emit additional hierarchical child models (e.g. a circular/inout block).
assert {test.vm_prefix, 'VTest'} <= models.keys(), models

test.compile(threads=threads,
             verilator_flags2=flags +
             ['--repcut', '--repcut-partitioner',
              partitioner(test, plans / '%p.csv')])
test.execute()
test.file_grep(test.obj_dir + '/VTest/VTest__stats.txt',
               r'RepCut native, replaced procedures\s+(\d+)', 4)
if threads > 1:
    profile = (Path(test.obj_dir) / 'profile.vlt').resolve()
    runtime = ['--repcut', '--repcut-partitioner', partitioner(test, plans / '%p.csv')]
    test.compile(threads=threads, verilator_flags2=flags + runtime + ['--prof-pgo'])
    test.execute(all_run_flags=['+verilator+prof+vlt+file+' + str(profile)])
    assert re.search(r'profile_data -model "VTest" -mtask "[^"]+" -cost 64\'d[1-9]',
                     profile.read_text(encoding="utf8"))
    # The top has no partition tasks. Profile records belong to the child model.
    test.compile(threads=threads, verilator_flags2=flags + runtime + [str(profile)])
    test.execute()
    test.file_grep_not(test.compile_log_filename, r'PROFOUTOFDATE')

# Exercise the default automatic plan at both serial and multithreaded settings.
test.compile(threads=threads, verilator_flags2=flags)
test.execute()
for prefix, count in models.items():
    paths = list(Path(test.obj_dir).rglob(prefix + '__repcut_early.partition/rcp_output.txt'))
    assert len(paths) == 1, (prefix, paths)
    assert len(paths[0].read_text(encoding="utf8").splitlines()) == count, prefix
test.passes()
