#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap
from repcut_common import partitioner

test.scenarios('vltmt')
# Internal graph and lowering reports are opt-in.
test.verilator_flags += ['--repcut-dump-graph']
test.top_filename = str(Path(test.top_filename).resolve())
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
for mode, threads in (('stock', 2), ('repcut', 1), ('repcut', 2), ('repcut', 4), ('protected', 2)):
    flags = ['--no-skip-identical', '--x-initial', '0', '--output-split-cfuncs', '32']
    if mode == 'protected':
        flags += ['--protect-ids', '--protect-key', 'REPCUT_CLONE']
    if mode != 'stock':
        test.compile(make_top_shell=False,
                     make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
        nodes = [
            line.split()
            for line in base.with_suffix('.graph').read_text(encoding="utf8").splitlines()[1:]
        ]
        predecessors = [[] for _ in nodes]
        for nid, node in enumerate(nodes):
            for successor in node[2:]:
                predecessors[int(successor)].append(nid)
        sinks = [nid for nid, node in enumerate(nodes) if float(node[1]) >= 0 and len(node) == 2]
        parts = [set() for _ in range(threads)]
        for ordinal, sink in enumerate(sinks):
            part = parts[ordinal % threads]
            pending = [sink]
            while pending:
                nid = pending.pop()
                if nid not in part:
                    part.add(nid)
                    pending.extend(predecessors[nid])
        membership = Path(test.obj_dir) / 'membership.csv'
        membership.write_text(''.join(','.join(map(str, sorted(part))) + '\n' for part in parts),
                              encoding="utf8")
        flags += ['-frepcut', '--repcut-partitioner', partitioner(test, membership)]
    else:
        flags += ['-fno-repcut']
    test.compile(make_top_shell=False,
                 make_main=False,
                 threads=threads,
                 verilator_flags2=flags + [
                     '--exe',
                     str(Path(test.pli_filename).resolve()), '-CFLAGS',
                     '-DCLONE_THREADS=' + str(threads), '-CFLAGS', '-DVL_THREADS_SERIAL_COST=0'
                 ])
    # This small fixture must dispatch workers before exercising clone hooks.
    test.execute()
test.passes()
