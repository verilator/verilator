// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Driss Hafdi.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   test #(.param(32'd0)) test_i;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module test
  #(
    parameter logic param = 1'b0
    ) ();
endmodule
