// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Composite sequence operators the per-attempt count engine cannot lower.

module t (
    input clk
);

  bit a;
  bit b;
  bit c;
  bit d;

  // verilog_format: off
  assert property (@(posedge clk) (a ##1 b) or (c ##2 d));

  cover property (@(posedge clk) (a ##[1:$] b) and (c ##1 d));

  // One done latch cannot identify ranged endpoints for overlapping attempts.
  assert property (@(posedge clk) (a ##[1:2] b) and (c ##2 d));

  assert property (@(posedge clk) (a ##1 b) |-> not (c ##[1:2] d)) $display("pass");

  assert property (@(posedge clk) ((|($random | $random))[*2]) and (1'b1 ##1 1'b1));

  assert property (@(posedge clk) (a[*2000]) and (1'b1 ##1 1'b1));

  assert property (@(posedge clk)
      (s_always [1:2] b) and (((a ##2 b) or (c ##2 d)) ##[1:300] a)) else $display("f");

  assert property (@(posedge clk) ##[1:$] (a until b));
  // verilog_format: on

endmodule
