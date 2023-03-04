// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in
   );

   parameter P32 = 32;
   parameter P24 = 24;
   localparam P29 = P24 + 5;

   input                clk;
   output reg [P24-1:0] out;

   input [P29 - 1:0]      in;

   always @(posedge clk) begin
      if (P29 >= P24) begin
         out <= in[P29 - 1 -: P24];
      end
      else begin
         out <= {{(P24 - P29){1'b0}}, in};
      end
   end
endmodule
