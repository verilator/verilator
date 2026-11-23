#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import csv
from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vlt_all')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
if not test.have_sc:
    test.skip('No SystemC installed')

threads = 2 if test.vltmt else 1
flags = ['--sc', '--stats', '--no-skip-identical', '--output-split-cfuncs', '64']
test.compile(make_main=False,
             threads=threads,
             verilator_flags2=flags + ['--exe', test.pli_filename])
test.execute()
test.compile(make_main=False,
             threads=threads,
             verilator_make_gmake=False,
             verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
assert 'complete 1\n' in base.with_suffix('.report.txt').read_text(encoding="utf8")
with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
    nodes = list(csv.DictReader(stream, delimiter='\t'))
deps = [[int(x) for x in node['inputs'].split(',') if x] for node in nodes]
with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
    for row in csv.DictReader(stream, delimiter='\t'):
        deps[int(row['node'])].append(int(row['predicate']))
parts = [set() for _ in range(threads)]
sinks = [
    int(node['id']) for node in nodes if node['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')
]
for ordinal, sink in enumerate(sinks):
    part = parts[ordinal % threads]
    pending = [sink]
    while pending:
        node = pending.pop()
        if node not in part:
            part.add(node)
            pending.extend(deps[node])
membership = Path(test.obj_dir) / 'membership.csv'
membership.write_text(''.join(','.join(map(str, sorted(part))) + '\n' for part in parts),
                      encoding="utf8")
test.compile(make_main=False,
             threads=threads,
             verilator_flags2=flags + [
                 '--repcut', '--repcut-partitioner',
                 partitioner(test, membership), '--exe', test.pli_filename
             ])
test.file_grep(test.stats, r'RepCut native, replaced procedures\s+(\d+)', 4)
test.file_grep(test.stats, r'RepCut native, SystemC input captures\s+(\d+)', 5)
test.execute()
test.passes()
