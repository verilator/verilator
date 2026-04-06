// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  logic a, b;

  always @(posedge clk) cyc <= cyc + 1;

  // Non-constant bounds
  a1: assert property (@(posedge clk) a |-> ##[1:cyc] b);

  // Negative bound
  a2: assert property (@(posedge clk) a |-> ##[-1:3] b);

  // Max < min
  a3: assert property (@(posedge clk) a |-> ##[5:2] b);

  // ##0 in range
  a4: assert property (@(posedge clk) a |-> ##[0:3] b);

  // Non-constant minimum in unbounded range
  a5: assert property (@(posedge clk) a |-> ##[cyc:$] b);

  // Negative minimum in unbounded range
  localparam int NEG = -1;
  a6: assert property (@(posedge clk) a |-> ##[NEG:$] b);

endmodule
