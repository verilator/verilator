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
# Generate explicit priority chains: loops could be lowered into muxes before
# reaching the guarded compilation splitter that this regression exercises.
rtl = Path(test.obj_dir) / 'priority.v'
lines = [
    'module t(input clk, reset, en, reverse, input [127:0] mask,',
    '         input [6:0] a, output reg [6:0] q, output reg [30:0] count);',
    'always @(posedge clk) begin', '  if (reset) q <= 0;', '  else if (en) begin',
    '    if (reverse) begin'
]
for reverse in (True, False):
    for ordinal, bit in enumerate(range(127, -1, -1) if reverse else range(128)):
        keyword = 'if' if ordinal == 0 else 'else if'
        operator = '+' if reverse else '^'
        lines.append(f"      {keyword} (mask[{bit}]) q <= (a {operator} 7'd{bit}) ^ count[6:0];")
    if reverse:
        lines.append('    end else begin')
lines += [
    '    end', '  end', 'end', 'always @(posedge clk) begin', '  if (reset) count <= 0;',
    "  else if (en) count <= count + {24'b0, q} + 31'd1;", 'end', 'endmodule'
]
rtl.write_text('\n'.join(lines) + '\n', encoding="utf8")
test.top_filename = str(rtl.resolve())
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
default_chunks = {}
for case, threads, limit, extra in [('native', 1, 256, []), ('small', 1, 32, []),
                                    ('parallel', 2, 64, []),
                                    ('protected', 2, 256, ['--protect-ids']),
                                    ('default', 1, None, []), ('explicit', 1, 4000, []),
                                    ('zero', 1, 0, []), ('previous', 1, 2000, []),
                                    ('default_parallel', 2, None, []),
                                    ('explicit_parallel', 2, 4000, [])]:
    flags = [
        '--assert', '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0',
        '--output-split', '512', '-CFLAGS', f'-DREPCUT_TEST_THREADS={threads}'
    ] + extra
    if limit is not None:
        flags += ['--output-split-cfuncs', str(limit)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
    with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
        nodes = list(csv.DictReader(stream, delimiter='\t'))
    dependencies = [[int(x) for x in n['inputs'].split(',') if x] for n in nodes]
    with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            dependencies[int(row['node'])].append(int(row['predicate']))
    parts = [set() for _ in range(threads)]
    sinks = [int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')]
    for ordinal, sink in enumerate(sinks):
        pending = [sink]
        part = parts[ordinal % threads]
        while pending:
            node = pending.pop()
            if node not in part:
                part.add(node)
                pending.extend(dependencies[node])
    membership = Path(test.obj_dir) / 'membership.csv'
    membership.write_text(''.join(','.join(map(str, sorted(p))) + '\n' for p in parts),
                          encoding="utf8")
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + [
                     '-frepcut', '--repcut-partitioner',
                     partitioner(test, membership), '--exe',
                     str(Path(test.pli_filename).resolve())
                 ])
    with base.with_suffix('.chunks.tsv').open(encoding="utf8") as stream:
        chunks = list(csv.DictReader(stream, delimiter='\t'))
    assert chunks and all(int(row['body_nodes']) <= (limit or 4000) for row in chunks)
    if case in ('default', 'default_parallel'):
        default_chunks[threads] = chunks
        assert any(int(row['body_nodes']) > 2000 for row in chunks)
    elif case in ('explicit', 'zero', 'explicit_parallel'):
        assert chunks == default_chunks[threads], 'Default and explicit RepCut budgets differ'
    if case == 'native':
        assert len(chunks) < 80, 'Priority chains fragmented into tiny functions'
    (Path(test.obj_dir) / (case + '.chunks.tsv')).write_text(
        base.with_suffix('.chunks.tsv').read_text(encoding="utf8"), encoding="utf8")
    subprocess.run(
        ['make', '-C',
         str(Path(test.obj_dir).resolve()), '-f', test.vm_prefix + '.mk', '-j2'],
        check=True)
    test.execute()
test.passes()
