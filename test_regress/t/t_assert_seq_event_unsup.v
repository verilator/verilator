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

  // Clockless `@seq` stays E_UNSUPPORTED even under a default clocking, matching
  // Questa; whether 9.4.2.4 should inherit it here is an open PR question.
  default clocking @(posedge clk);
  endclocking

  // verilog_format: off
  sequence s_unclocked;
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
    @s_unclocked;
    @s_nonedge;
    @s_noncons;
  end
endmodule
