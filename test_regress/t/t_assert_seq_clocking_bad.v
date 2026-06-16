// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
module t (
    input clk,
    input clk2
);
  logic a, b;

  sequence s_multi;
    @(posedge clk) a;
  endsequence

  sequence s_nest;
    @(posedge clk) b;
  endsequence

  sequence s_level;
    @clk a;
  endsequence

  // Multiclocked: explicit assertion clock differs from the sequence clock.
  assert property (@(posedge clk2) s_multi);

  // Clocking event nested inside a larger sequence expression.
  assert property (s_nest ##1 a);

  // Non-edge clocking event on a sequence.
  assert property (s_level);

endmodule
