// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Planner corner shapes: negated liveness pass, single-cycle cover abort, strong cover or

module t (
    input clk
);

  logic a = 0, b = 0, c = 0, x = 0;
  int cyc = 0;
  int np1 = 0, nf1 = 0, nc2 = 0, nc3 = 0, nf4 = 0, nc5 = 0;

  // verilog_format: off
  assert property (@(posedge clk) not (##[1:$] b)) np1 = np1 + 1; else nf1 = nf1 + 1;

  cover property (@(posedge clk) accept_on (x) c) nc2 = nc2 + 1;

  cover property (@(posedge clk) (s_always [1:2] a) or (s_always [1:2] c)) nc3 = nc3 + 1;

  assert property (@(posedge clk) ((a ##2 b) or (c ##2 b)) |-> s_always [1:2] a) else nf4 = nf4 + 1;

  cover property (@(posedge clk) sync_accept_on (x) c) nc5 = nc5 + 1;
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
`ifdef TEST_VERBOSE
    $display("np1=%0d nf1=%0d nc2=%0d nc3=%0d nf4=%0d nc5=%0d", np1, nf1, nc2, nc3, nf4, nc5);
`endif
    if (np1 != 0) $stop;
    // Unbounded attempts merge: one fail action per failing cycle, per-attempt would be 11
    if (nf1 != 2) $stop;
    if (nc2 != 1) $stop;  // Other simulator: 15
    if (nc3 != 5) $stop;
    if (nf4 != 0) $stop;
    if (nc5 != 1) $stop;  // Other simulator: 15
    $write("*-* All Finished *-*\n");
  end
endmodule
