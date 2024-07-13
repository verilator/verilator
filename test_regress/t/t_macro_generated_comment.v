// DESCRIPTION: Verilator: Test comment generated from macro
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define FOO() /``* some_vendor_comment macro generated *``/

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   `FOO()

   // Test loop
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
