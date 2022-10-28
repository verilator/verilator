// DESCRIPTION::Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   typedef struct packed {
      logic signed [63:0] b;
   } a_t;

   a_t a_r;
   a_t a_n;
   logic signed [63:0]    b;
   logic                  res;

   assign b = a_r.b;

   always_comb begin
      a_n = a_r;
      res = '0;
      if (b inside {1, 2}) begin
         res = 1'b1;
      end
   end

   always_ff @(posedge clk) begin
      a_r <= a_n;
   end

endmodule
