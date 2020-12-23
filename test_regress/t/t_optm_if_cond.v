// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   q0, q1, q2, q3, q4,
   // Inputs
   clk, rst, en, i0, i1, i2, i3, i4
   );
   input clk;

   input rst;
   input en;
   output int q0;   input int i0;
   output int q1;   input int i1;
   output int q2;   input int i2;
   output int q3;   input int i3;
   output int q4;   input int i4;

   always @ (posedge clk) begin
      if (rst) begin
         if (en) q0 <= i0;
      end
      else q0 <= 0;

      if (rst) begin
         if (en) q1 <= i1;
      end
      else q1 <= 0;

      if (rst) begin
         if (en) q2 <= i2;
      end
      else q2 <= 0;

      if (rst) begin
         if (en) q3 <= i3;
      end
      else q3 <= 0;
   end

   always_comb begin
      q4 = i4;
      if (q4 == 0) begin
         // Conflicts with condition
         q4 = 1;
      end
      if (q4 == 0) begin
         // Conflicts with condition
         q4 = 2;
      end
   end

endmodule
