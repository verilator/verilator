// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct {
  logic [31:0] val;
  logic [31:0] other;
} St1;

typedef struct {
  St1 inner;
  logic [31:0] tail;
} St2;

module m;
  St2 st2;
  St2 forced;
  St2 snapshot;
  initial begin
    st2.inner.val = 32'h11;
    st2.inner.other = 32'h12;
    st2.tail = 32'h13;
    forced.inner.val = 32'h21;
    forced.inner.other = 32'h22;
    forced.tail = 32'h23;
    force st2 = forced;
    snapshot = st2;
    `checkh(snapshot.inner.val, 32'h21);
    `checkh(snapshot.inner.val[0], 1'b1);
    force st2.inner.val = 32'h30;
    release st2.inner.val;
    snapshot = st2;
    `checkh(snapshot.inner.val, 32'h21);
    `checkh(snapshot.inner.val[0], 1'b1);
    `checkh(snapshot.inner.other, 32'h22);
    `checkh(snapshot.tail, 32'h23);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
