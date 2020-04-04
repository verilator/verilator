// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   const logic [2:0] five = 3'd5;

   always @ (posedge clk) begin
      five = 3'd4;
      if (five !== 3'd5) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
