// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off MULTITOP */

// Bad: ##0 as intra-assignment delay (IEEE 1800-2023 14.11)
module has_clocking;
  logic clk = 0;
  logic out;
  default clocking cb @(posedge clk);
  endclocking
  always out <= ##0 1;
endmodule

// Bad: ##0 without default clocking (IEEE 1800-2023 14.11)
module no_clocking;
  initial ##0;
endmodule
