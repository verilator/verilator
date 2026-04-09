// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  logic a, b;

  // Unsupported: nonconsecutive rep inside throughout
  assert property (@(posedge clk) a throughout (b[=2]))
    else $error("FAIL");

  initial begin #100; $finish; end
endmodule
