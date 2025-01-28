// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   num_zeros, num_ones,
   // Inputs
   clk, reset_l, vec
   );

   input logic clk;
   input logic reset_l;
   input logic [7:0] vec;
   output logic [7:0] num_zeros;
   output logic [7:0] num_ones;

   always_comb begin
      num_zeros = '0;
      num_ones = '0;
      for (int i = 0; i < 8; i++) begin
         if (vec[i] == 0) begin
            num_zeros++;
         end else begin
            num_ones++;
         end
      end
   end
   assert property (@(negedge clk) disable iff (~reset_l) (num_ones == $countones(vec)));
   assert property (@(negedge clk) disable iff (~reset_l) (num_zeros == $countbits(vec, '0)));
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
