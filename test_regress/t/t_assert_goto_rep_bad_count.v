// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  logic a, b;
  int n;

  // Error: non-constant count
  assert property (@(posedge clk) a[->n] |-> b)
    else $error("FAIL");

  // Error: zero count
  assert property (@(posedge clk) a[->0] |-> b)
    else $error("FAIL");

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
