// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

`define HIER_BLOCK /*verilator hier_block*/

interface byte_ifs(input clk);
   logic [7:0] data;
   modport sender(input clk, output data);
   modport receiver(input clk, input data);
endinterface;


module t (/*AUTOARG*/
   // Inputs
   clk
   ); `HIER_BLOCK // Top module can not be a hierarchy block
   input wire clk;

   wire [7:0] out0;
   int count = 0;

   byte_ifs in_ifs(.clk(clk));
   byte_ifs out_ifs(.clk(clk));
   assign in_ifs.data = out0;

   sub0 i_sub0(.clk(clk), .in(count), .out(out0));
   sub1 i_sub1(.in(in_ifs), .out(out_ifs));

endmodule

module sub0 (
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   logic [7:0] ff;

   always_ff @(posedge clk) ff <= in;
   assign out = ff;
endmodule

module sub1 (byte_ifs.receiver in, byte_ifs.sender out); `HIER_BLOCK
   assign out.data = in.data;
endmodule
