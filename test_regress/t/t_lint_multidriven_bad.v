// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   out, out2,
   // Inputs
   clk, a0, d0, d1
   );

   input clk;
   input [1:0] a0;
   input [7:0] d0;
   input [7:0] d1;
   output reg [31:0] out;
   output reg [15:0] out2;

   reg [7:0] 	     mem [4];

   always @(posedge clk) begin
      mem[a0] <= d0;
   end
   always @(negedge clk) begin
      mem[a0] <= d1;
   end
   assign out = {mem[3],mem[2],mem[1],mem[0]};

   always @(posedge clk) begin
      out2[7:0] <= d0;
   end
   always @(negedge clk) begin
      out2[15:8] <= d0;
   end
   
endmodule
