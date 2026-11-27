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
rtl = Path(test.obj_dir) / 'hybrid.v'
terms = [f"(data / (denom | 32'd{2 * i + 1}))" for i in range(24)]
rtl.write_text('''module t(input clk, reset, enable, event_enable,
    input [31:0] data, denom, input [1:0] address,
    output reg [31:0] q, r, output reg [767:0] wide,
    output [31:0] observed, mem_out);
`ifdef REPCUT_GRAPH_ONLY
  assign q = 0;
  assign r = 0;
  assign observed = 0;
  assign mem_out = 0;
  always @(posedge clk) begin
    if (reset) wide <= 0;
    else if (enable) wide <= {''' + ','.join(terms) + '''};
  end
`else
  wire [31:0] expensive = ''' + ' ^ '.join(terms) + ''';
  wire [31:0] shared_value = (expensive + data) ^ q;
  reg [31:0] mem [0:2];
  assign mem_out = address < 3 ? mem[address] : 0;
  assign observed = shared_value ^ r;
  always @(posedge clk) begin
    if (reset) begin q <= 0; r <= 7; end
    else if (enable) begin q <= shared_value + r; r <= q ^ data; end
    if (event_enable && data[1]) $display("SOURCE %0d %0d", q, shared_value);
  end
  always @(posedge clk) begin
    if (reset) wide <= 0;
    else if (enable) wide <= {''' + ','.join(f"(shared_value / (denom | 32'd{2 * i + 1}))"
                                             for i in range(24)) + '''};
    if (enable && address < 3) mem[address] <= shared_value ^ wide[31:0];
    if (event_enable && data[0]) $display("GRAPH %0d %0d", wide[31:0], ''' +
               ' ^ '.join(f"(shared_value / (denom | 32'd{2 * i + 1}))" for i in range(24)) + ''');
  end
`endif
endmodule
''',
               encoding="utf8")
test.top_filename = str(rtl.resolve())
base = Path(test.obj_dir) / (test.vm_prefix + '__repcut_early')
references = {}
for case, threads, extra in [('stock', 1, []), ('serial', 1, []), ('parallel', 2, []),
                             ('four', 4, []), ('protected', 2, ['--protect-ids']),
                             ('stock_graph', 1, []), ('graph_serial', 1, []),
                             ('graph_parallel', 4, [])]:
    graph = 'graph' in case
    flags = [
        '--assert', '--stats', '--no-skip-identical', '--x-initial', '0', '--x-assign', '0',
        '-fno-dfg', '--output-split-cfuncs', '64', '--output-split', '512', '-CFLAGS',
        f'-DREPCUT_TEST_THREADS={threads}'
    ] + extra
    if graph:
        flags += ['-DREPCUT_GRAPH_ONLY', '-CFLAGS', '-DREPCUT_GRAPH_ONLY']
    runtime = ['-fno-repcut']
    if not case.startswith('stock'):
        test.compile(make_main=False,
                     verilator_make_gmake=False,
                     threads=threads,
                     verilator_flags2=flags + ['-fno-repcut', '--repcut-dump-graph'])
        with base.with_suffix('.nodes.tsv').open(encoding="utf8") as stream:
            nodes = list(csv.DictReader(stream, delimiter='\t'))
        dependencies = [[int(x) for x in row['inputs'].split(',') if x] for row in nodes]
        with base.with_suffix('.controls.tsv').open(encoding="utf8") as stream:
            for row in csv.DictReader(stream, delimiter='\t'):
                dependencies[int(row['node'])].append(int(row['predicate']))
        parts = [set() for _ in range(threads)]
        sinks = [
            int(n['id']) for n in nodes if n['kind'] in ('NEXT', 'OUTPUT', 'MEMWRITE', 'EFFECT')
        ]
        for ordinal, sink in enumerate(sinks):
            # Keep both source and exceptional clocked procedures together;
            # distribute output cones to exercise cross-partition old-state reads.
            owner = ordinal % threads if nodes[sink]['kind'] == 'OUTPUT' else 0
            pending = [sink]
            while pending:
                node = pending.pop()
                if node not in parts[owner]:
                    parts[owner].add(node)
                    pending.extend(dependencies[node])
        membership = Path(test.obj_dir) / 'membership.csv'
        membership.write_text(''.join(','.join(map(str, sorted(p))) + ',\n' for p in parts),
                              encoding="utf8")
        runtime = ['-frepcut', '--repcut-partitioner', partitioner(test, membership)]
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 threads=threads,
                 verilator_flags2=flags + runtime +
                 ['--exe', str(Path(test.pli_filename).resolve())])
    if case in ('serial', 'four'):
        # Graph islands are optimized again when joined to source procedures.
        # Their deleted AST nodes must not leave stale chunk-size cache entries.
        def emitted():
            return {
                p.name: p.read_bytes()
                for pattern in ('*.cpp', '*.h', '*.chunks.tsv', '*.cuts.tsv')
                for p in Path(test.obj_dir).glob(pattern)
            }

        reference = emitted()
        for debug in (3, 0):
            test.compile(make_main=False,
                         verilator_make_gmake=False,
                         threads=threads,
                         verilator_flags2=flags + runtime + [
                             '--debugi-V3RepCutEmit',
                             str(debug), '--exe',
                             str(Path(test.pli_filename).resolve())
                         ])
            assert emitted() == reference, 'Chunk emission depends on compiler allocation history'
    if not case.startswith('stock'):
        stats = Path(test.stats).read_text(encoding="utf8")
        (Path(test.obj_dir) / (case + '.stats')).write_text(stats, encoding="utf8")
        keys = ('graph fallback programs', ) if graph else ('hybrid programs',
                                                            'graph combinational drivers',
                                                            'graph clocked procedures',
                                                            'clocked procedures')
        for key in keys:
            match = re.search(r'RepCut native source, ' + key + r'\s+(\d+)', stats)
            assert match and int(match[1]) > 0, (case, key)
        if not graph:
            assert 'RepCut native source, graph fallback programs' not in stats, case
        with base.with_suffix('.chunks.tsv').open(encoding="utf8") as stream:
            assert all(
                int(row['body_nodes']) <= 64 for row in csv.DictReader(stream, delimiter='\t'))
    subprocess.run(['make', '-C', test.obj_dir, '-f', test.vm_prefix + '.mk', '-j2'], check=True)
    run = subprocess.run([str(Path(test.obj_dir).resolve() / test.vm_prefix)],
                         capture_output=True,
                         text=True,
                         timeout=30,
                         check=False)
    output = run.stdout + run.stderr
    (Path(test.obj_dir) / (case + '.log')).write_text(output, encoding="utf8")
    run.check_returncode()
    assert '*-* All Finished *-*' in output
    # Active-region ordering between independent always blocks is unspecified.
    # Compare each block's effects within every cycle, including inactive cycles.
    cycles = {}
    cycle = None
    for line in output.splitlines():
        if line.startswith('CYCLE '):
            cycle = int(line.split()[1])
            cycles[cycle] = []
        elif line.startswith(('SOURCE ', 'GRAPH ')):
            cycles[cycle].append(line)
    observed = {cycle: sorted(lines) for cycle, lines in cycles.items()}
    assert len(observed) == 4096
    if graph not in references:
        references[graph] = observed
    else:
        assert observed == references[graph], case
test.passes()
