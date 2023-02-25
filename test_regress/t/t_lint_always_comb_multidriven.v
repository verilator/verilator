// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   out1, out2, out3, out4, out5, out6, out7, out8,
   // Inputs
   clk, d
   );

   input clk;
   input d;
   output reg out1;
   output reg out2;
   output reg out3;
   output reg out4;
   output reg out5;
   output reg out6;
   output reg out7;
   output reg out8;

   assign out1 = 1'b0;
   always_comb out1 = d;  // <--- Warning

   assign out2 = d;
   always_comb out2 = 1'b0;  // <--- Warning

   always_comb out3 = d;
   assign out3 = 1'b0;  // <--- Warning

   always_comb out4 = 1'b0;
   assign out4 = d;  // <--- Warning

   always_comb out5 = 1'b0;
   always_comb out5 = d;  // <--- Warning

   always_comb out6 = d;
   always_comb out6 = 1'b0;  // <--- Warning

   always_comb begin
      out7 = 1'b0;
      out7 = d;
   end

   always_comb begin
      out8 = d;
      out8 = 1'b0;
   end

   reg [1:0] arr_packed;
   reg arr_unpacked [0:1];
   reg [1:0] gen_arr_packed;
   reg gen_arr_unpacked [0:1];
   genvar g;

   always_comb begin
      arr_packed[0] = d;
      arr_packed[1] = d;
   end

   always_comb begin
      arr_unpacked[0] = d;
      arr_unpacked[1] = d;
   end

   generate
      for (g=0; g<2; ++g) begin
         always_comb gen_arr_packed[g] = d;
         always_comb gen_arr_unpacked[g] = d;
      end
   endgenerate

endmodule
