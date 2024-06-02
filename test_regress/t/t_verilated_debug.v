// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [95:0] wide;

   initial begin
      // internal code coverage for _vl_debug_print_w
      wide = {32'haa, 32'hbb, 32'hcc};
      $c("_vl_debug_print_w(", $bits(wide), ", ", wide, ");");
   end

   // Test loop
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
