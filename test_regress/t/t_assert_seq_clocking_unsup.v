// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
  input clk,
  input clk2
);
  logic a, b;

  // verilog_format: off
  sequence s_multi;
    @(posedge clk) a;
  endsequence

  sequence s_nest;
    @(posedge clk) b;
  endsequence
  // verilog_format: on

  assert property (@(posedge clk2) s_multi);
  assert property (s_nest ##1 a);

  // Clocking event both before and after disable iff
  property p_double_clock;
    @(posedge clk) disable iff (a) @(posedge clk2) not b;
  endproperty

  assert property (p_double_clock);
  cover property (@(posedge clk) disable iff (a) @(posedge clk2) strong(b));

endmodule
