// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in
   );

   input clk;
   input [2:0] in;
   output [2:0] out;

   logic [2:0] r_in;
   always_ff @ (posedge clk) r_in <= in;

   flop p0 (.clk(clk), .d(r_in[0]), .q(out[0]));
   flop p2 (.clk(r_in[1]), .d(clk), .q(out[1]));
   flop p1 (.clk(clk), .d(r_in[2]), .q(out[2]));

endmodule

module flop
  (
   input  d,
   input  clk,
   output logic q);

   // verilator no_inline_module

   always_ff @ (posedge clk) begin
      q <= d;
   end
endmodule
