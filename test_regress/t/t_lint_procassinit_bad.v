// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk, reset_l, in, enable
   );
   input clk;
   input reset_l;
   input in;
   input enable;

   logic ok1 = 1;
   logic ok2 = 1;
   logic ok3 = ok2;

   initial begin
      ok1 = 1;
   end

   //== Faulty example

   logic flop_out = 1;  // <--- Warning

   always @(posedge clk, negedge reset_l) begin
      if (enable) begin
         flop_out <= ~in;  // <--- Use of initialized
      end
   end

   //== Fixed example

   logic flop2_out;

   always @(posedge clk, negedge reset_l) begin
      if (!reset_l) begin
         flop2_out <= '1;  // <--- Added reset init
      end
      else if (enable) begin
         flop2_out <= ~in;
      end
   end

   // Combo version
   logic bad_comb = 1;    // but this is not fine

   always @* begin
      bad_comb = ok2;
   end

   wire _unused_ok = &{1'b0, flop_out, flop2_out, bad_comb, ok1, ok2, ok3};

endmodule
