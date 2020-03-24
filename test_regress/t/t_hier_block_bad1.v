// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

`define HIER_BLOCK /*verilator hier_block*/

module t (/*AUTOARG*/
   // Inputs
   clk
   ); `HIER_BLOCK // Top module can not be a hierarchy block
   input wire clk;

   wire [7:0] out0;
   int count = 0;

   sub0 i_sub0(.clk(clk), .in(count), .out(out0));

endmodule

module sub0 (
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   logic [7:0] ff;

   always_ff @(posedge clk) ff <= in;
   assign out = ff;
endmodule
