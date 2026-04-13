// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  bit clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    #300;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  // Complicated way to write constant 0 that only Dfg can decipher
  wire [1:0] constant = 2'b0 ^ (({2{clk}} & ~{2{clk}}));

  always @(posedge constant[0]) begin
    $stop;
  end

endmodule
