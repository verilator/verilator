// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
  input clk
);
  bit a, b;
  logic g = 0;

  // verilog_format: off
  sequence s_clockless;
    a ##1 b;
  endsequence

  sequence s_nonedge;
    @(g) a ##1 b;
  endsequence

  sequence s_noncons;
    @(posedge clk) a[=2];
  endsequence
  // verilog_format: on

  initial begin
    @s_clockless;
    @s_nonedge;
    @s_noncons;
  end
endmodule
