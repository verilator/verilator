// DESCRIPTION: Verilator: Verilog Test module
//
// This test verifies that a top-module can be specified which
// is instantiated beneath another module in the compiled source
// code, even when that top-module has a module both above and beside
// it in the hierarchy.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Dan Petrisko.
// SPDX-License-Identifier: CC0-1.0

module top(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   always_ff @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish();
   end

   under under();

endmodule

module under(/*AUTOARG*/
   );

endmodule

module faketop(/*AUTOARG*/
   );

   under under();
   top top();

   // Stop immediately if this module is instantiated
   initial begin
     $stop();
   end

endmodule
