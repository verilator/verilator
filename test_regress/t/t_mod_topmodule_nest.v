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

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

endmodule

module under(/*AUTOARG*/
   );

endmodule

module top(/*AUTOARG*/
   );

   under under();

endmodule

module faketop(/*AUTOARG*/
   );

   under under();
   top top();

endmodule
