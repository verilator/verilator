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

  default clocking @(posedge clk);
  endclocking

  // verilog_format: off
  sequence s_nonedge;
    @(g) a ##1 b;
  endsequence

  sequence s_ref;
    @(posedge clk) a;
  endsequence
  // verilog_format: on

  // Legal: p is never asserted, so s_ref stays referenced outside any
  // assertion property, which is not yet supported.
  property p;
    s_ref;
  endproperty

  initial begin
    @s_nonedge;
  end
endmodule
