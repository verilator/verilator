// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   logic oe;

   read r (.clk(clk), .data( ( ( oe == 1'd001 ) && implicit_write ) ) );
   set  s (.clk(clk), .enable(implicit_write));
   set  u (.clk(clk), .enable(~implicit_also));

endmodule

module set (
   input  clk,
   output enable
   );

endmodule

module read (
   input clk,
   input data
   );

endmodule
