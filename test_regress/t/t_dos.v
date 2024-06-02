// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// This file has DOS carrage returns in it!
module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
// This file has DOS carrage returns in it!
