// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   dataout,
   // Inputs
   clk, sel, d0, d1
   );

   input clk;
   input sel;

   logic [7:0] data [1:0][3:0];
   input [7:0] d0, d1;

   output wire [8*2*4-1:0] dataout;

   always_comb begin
      for ( integer j = 0; j <= 1; j++ ) begin
         if (sel)
           data[j] = '{ d0, d1, 8'h00, 8'h00 };
         else
           data[j] = '{ 8'h00, 8'h00, 8'h00, 8'h00 };
      end
      for ( integer j = 0; j <= 1; j++ ) begin
         data[j] = sel
                   ? '{ d0, d1, 8'h00, 8'h00 }
                   : '{ 8'h00, 8'h00, 8'h00, 8'h00 };
      end
   end

   assign dataout = {data[0][0], data[0][1], data[0][2], data[0][3],
                     data[1][0], data[1][1], data[1][2], data[1][3]};

endmodule
