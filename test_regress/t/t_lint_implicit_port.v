// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   logic oe;

   read r (.clk(clk), .data( ( ( oe == 1'd001 ) && implicit_write ) ) );
   sets s (.clk(clk), .enable(implicit_write));
   read u (.clk(clk), .data(~implicit_also));

endmodule

module sets (
   input  clk,
   output enable
   );
   assign enable = 1'b0;
endmodule

module read (
   input clk,
   input data
   );

endmodule
