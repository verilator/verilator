// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Corner shapes: negated liveness, single-cycle cover abort, strong cover or

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  logic a = 0, b = 0, c = 0, x = 0;
  int cyc = 0;
  int np1 = 0, nf1 = 0, nc2 = 0, nc3 = 0, nf4 = 0, nc5 = 0, np6 = 0, nf6 = 0;
  int nc9 = 0, nf10 = 0, np11 = 0, nf12 = 0, nf13 = 0, nf14 = 0;
  int np15 = 0, nf15 = 0, nf16 = 0, nc17 = 0, nf18 = 0;

  // verilog_format: off
  assert property (@(posedge clk) not (##[1:$] b)) np1 = np1 + 1; else nf1 = nf1 + 1;

  cover property (@(posedge clk) accept_on (x) c) nc2 = nc2 + 1;

  cover property (@(posedge clk) (s_always [1:2] a) or (s_always [1:2] c)) nc3 = nc3 + 1;

  assert property (@(posedge clk) ((a ##2 b) or (c ##2 b)) |-> s_always [1:2] a) else nf4 = nf4 + 1;

  cover property (@(posedge clk) sync_accept_on (x) c) nc5 = nc5 + 1;

  assert property (@(posedge clk) disable iff ($sampled(a) || $sampled(c)) not (b ##1 !b)) np6 = np6 + 1; else nf6 = nf6 + 1;

  cover property (@(posedge clk) a |-> (!c until b)) nc9 = nc9 + 1;

  assert property (@(posedge clk) sync_accept_on (x) (a |-> (b ##[1:2] (c ##1 a)))) else nf10 = nf10 + 1;

  assert property (@(posedge clk) sync_accept_on (x) (a ##[1:$] b)) np11 = np11 + 1;

  assert property (@(posedge clk) sync_accept_on (x) ((a ##[1:2] (b ##1 c)) ##1 a)) else nf12 = nf12 + 1;

  assert property (@(posedge clk) sync_accept_on (x) (a ##1 (b ##[1:2] (c ##1 a)))) else nf13 = nf13 + 1;

  assert property (@(posedge clk) sync_accept_on (x) (always [0:$] b)) else nf14 = nf14 + 1;

  assert property (@(posedge clk) disable iff ($sampled(a && $sampled(c))) not (b ##1 !b)) np15 = np15 + 1; else nf15 = nf15 + 1;

  assert property (@(posedge clk) accept_on (x) (a ##1 b)) else nf16 = nf16 + 1;

  cover property (@(posedge clk) sync_accept_on (x) (a ##1 b)) nc17 = nc17 + 1;

  assert property (@(posedge clk) (a ##[1:$] b) ##1 c) else nf18 = nf18 + 1;
  // verilog_format: on

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= (cyc >= 8 && cyc <= 13);
    b <= (cyc == 2) || (cyc == 10);
    c <= (cyc == 4);
    x <= (cyc == 4);
    if (cyc == 20) $finish;
  end

  final begin
    `checkd(np1, 0);  // zero-ok: unbounded not() never resolves to a pass
    `checkd(nf1, 2);  // One other sim: 11
    `checkd(nc2, 1);  // One other sim: 15
    `checkd(nc3, 5);
    `checkd(nf4, 0);
    `checkd(nc5, 1);  // One other sim: 15
    `checkd(np6, 12);
    `checkd(nf6, 1);
    `checkd(nc9, 1);  // One other sim: 3
    `checkd(nf10, 6);
    `checkd(np11, 2);  // One other sim: 3
    `checkd(nf12, 19);
    `checkd(nf13, 19);
    `checkd(nf14, 17);  // One other sim: 19
    `checkd(np15, 18);
    `checkd(nf15, 2);
    `checkd(nf16, 18);
    `checkd(nc17, 2);  // One other sim: 6
    `checkd(nf18, 14);
    $write("*-* All Finished *-*\n");
  end
endmodule
