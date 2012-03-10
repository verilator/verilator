// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.
// See bug408

module top
  (
   output logic [1:0] q,
   input logic [1:0]  d,
   input logic 	      clk
   );

   genvar 	     i;
   assign 	     q[i] = d[i];
endmodule

