// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

// Also check that SystemC is ordering properly
// verilator lint_on IMPERFECTSCH

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   input 	i1;
   input [7:0]	i8;
   input [15:0]	i16;
   input [31:0]	i32;
   input [63:0]	i64;
   input [64:0]	i65;

   output 	 o1;
   output [7:0]  o8;
   output [15:0] o16;
   output [31:0] o32;
   output [63:0] o64;
   output [64:0] o65;

   always @ (posedge clk) begin
      o1 <= i1;
      o8 <= i8;
      o16 <= i16;
      o32 <= i32;
      o64 <= i64;
      o65 <= i65;
   end

endmodule
