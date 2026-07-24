#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

import os

test.scenarios('vlt')

# 2000 signals; table-loop avoids per-var superlinear O(n²) registration.
N = 2000

gen_v = test.obj_dir + "/t_vpi_public_table_scale_gen.v"
os.makedirs(test.obj_dir, exist_ok=True)
with open(gen_v, "w", encoding="utf8") as fh:
    fh.write("module t(input wire clk, input wire [31:0] din, output wire [31:0] dout);\n")
    fh.write("  wire [31:0] _zz_0;\n")
    fh.write("  assign _zz_0 = din + 32'd0;\n")
    for i in range(1, N):
        fh.write("  wire [31:0] _zz_%d;\n" % i)
        fh.write("  assign _zz_%d = _zz_%d + 32'd%d;\n" % (i, i - 1, i % 256))
    fh.write("  reg [31:0] acc;\n")
    fh.write("  always @(posedge clk) acc <= _zz_%d;\n" % (N - 1))
    fh.write("  assign dout = acc;\n")
    fh.write("endmodule\n")

test.top_filename = gen_v

test.compile(verilator_flags2=["--vpi --public-flat-rw --stats"])

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

test.file_grep(syms, r'varsInsertFromTable')
test.file_grep_count(syms, r'->varInsert\(', 0)

syms_bytes = os.path.getsize(syms)
budget = 4 * 1024 * 1024
if syms_bytes > budget:
    test.error("Syms too large: %d > %d bytes" % (syms_bytes, budget))

test.passes()
