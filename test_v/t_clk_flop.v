// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`include "verilated.v"

module t_clk_flop (/*AUTOARG*/
   // Outputs
   q, q2,
   // Inputs
   clk, clk2, a
   );
   parameter WIDTH=8;
   input clk;
   input clk2;
   input [(WIDTH-1):0]  a;
   output [(WIDTH-1):0] q;
   output [(WIDTH-1):0] q2;
   reg [(WIDTH-1):0] q;
   reg [(WIDTH-1):0] q2;
   always @ (posedge clk) q<=a;
   always @ (posedge clk2) q2<=a;
endmodule
