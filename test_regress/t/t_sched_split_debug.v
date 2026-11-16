// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Split pieces of the debug-only trigger dump functions must stay under VL_DEBUG
module t;
  logic clk = 0;
  int cyc = 0;
  int neg = 0;
  always #5 clk = ~clk;

  always @(posedge clk) cyc <= cyc + 1;
  always @(negedge clk) neg <= neg + 1;

  initial begin
    repeat (4) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
