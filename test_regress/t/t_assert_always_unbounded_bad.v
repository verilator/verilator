// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a;

  // A strong always must be bounded (IEEE 1800-2023 16.12.11): there is no bare
  // s_always grammar production, and s_always [m:$] is the explicit "// Illegal"
  // example (p5). Both forms are rejected.
  assert property (@(posedge clk) s_always a);
  assert property (@(posedge clk) s_always [2:$] a);

  // A weak always range may only place $ on the high bound; an unbounded low
  // bound is not a legal cycle_delay_const_range_expression.
  assert property (@(posedge clk) always [$:5] a);

endmodule
