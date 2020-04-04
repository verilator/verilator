// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   t_multitop1s s ();
   initial $display("In '%m'");
   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
