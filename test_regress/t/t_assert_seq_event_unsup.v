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
  sequence s_nonedge;
    @(g) a ##1 b;
  endsequence

  sequence s_arg(x);
    @(posedge clk) x;
  endsequence
  // verilog_format: on

  task automatic f;
    bit x = 1;
    @(s_arg(x));
  endtask

  initial begin
    @s_nonedge;
    f();
  end
endmodule
