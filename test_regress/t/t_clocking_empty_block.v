// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Alex Mykyta.
// SPDX-License-Identifier: CC0-1.0

module t();
   logic clk = 0;
   logic x;
   logic y;
   always #1ns clk = ~clk;
   clocking cb @(posedge clk);
      output #1ns x;
      input  #1step y;
   endclocking
   initial begin
      repeat(10) @(posedge clk);
      $display("*-* All Finished *-*");
      $finish();
   end
endmodule
