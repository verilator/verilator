#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
import os
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = 't/t_hier_block_perf.v'
test.sim_time = 2000
flags = [
    '-fno-repcut', '--hierarchical', '--stats', '--no-skip-identical', 't/t_pgo_threads_hier.vlt',
    '-Wno-UNOPTFLAT', '-DSIM_CYCLES=100'
]

# Four outer threads permit simultaneous calls to the two-worker child models.
# With only two outer threads the hierarchy serializes these calls.
test.compile(threads=4, verilator_flags2=flags)
test.execute()

child = Path(test.obj_dir) / 'VTest'
base = child / 'VTest__repcut_early'
command = [
    'perl', os.environ['VERILATOR_ROOT'] + '/bin/verilator', '-f',
    test.obj_dir + '/VTest__hierMkArgs.f', '--stats', '--no-skip-identical'
]
test.run(logfile=str(child / 'native-probe.log'),
         cmd=command + ['-fno-repcut', '--repcut-dump-graph'],
         verilator_run=True)
assert 'native_threads 2\n' in base.with_suffix('.report.txt').read_text(encoding="utf8")
with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
    nodes = list(csv.DictReader(stream, delimiter='\t'))
deps = [[int(x) for x in node['inputs'].split(',') if x] for node in nodes]
with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
    for row in csv.DictReader(stream, delimiter='\t'):
        deps[int(row['node'])].append(int(row['predicate']))
parts = [set(), set()]
sinks = [
    int(node['id']) for node in nodes if node['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')
]
for ordinal, sink in enumerate(sinks):
    part = parts[ordinal % 2]
    pending = [sink]
    while pending:
        node = pending.pop()
        if node not in part:
            part.add(node)
            pending.extend(deps[node])
assert set().union(*parts) == set(range(len(nodes)))
membership = (child / 'native-membership.csv').resolve()
membership.write_text(''.join(','.join(map(str, sorted(part))) + '\n' for part in parts),
                      encoding="utf8")
test.run(logfile=str(child / 'native-compile.log'),
         cmd=command + ['--repcut', '--repcut-partitioner',
                        partitioner(test, membership)],
         verilator_run=True)
test.run(logfile=test.obj_dir + '/mixed-build.log',
         cmd=['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'])
test.file_grep(str(child / 'VTest__stats.txt'), r'RepCut native, replaced procedures\s+(\d+)', 19)
top_cpp = ''.join(path.read_text(encoding="utf8") for path in Path(test.obj_dir).glob('*.cpp'))
child_cpp = ''.join(path.read_text(encoding="utf8") for path in child.glob('*.cpp'))
assert '->addTask(' in top_cpp
# The child uses master's ExecGraph fixed-thread schedule instead of the old
# fixed-task mailbox.
assert '__Vthread__' in child_cpp and 'vl_invokeExecGraph' in child_cpp
test.execute()
assert Path(test.run_log_filename).read_text(encoding="utf8").count('sum=8977713eb467bc86') == 4
test.passes()
