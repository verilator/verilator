// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input wire reset_l,
   input wire clk
   );

   sub sub_I
     (
      .clk(clk),
      .reset_l(reset_l),
      .cpu_if_timeout(1'b0)
      );
endmodule

module sub
  (
   input wire   clk, reset_l,
   output reg   cpu_if_timeout
   );

   always @(posedge clk) begin
      if (!reset_l) begin
         cpu_if_timeout <= 1'b0;
      end
      else begin
         cpu_if_timeout <= 1'b0;
      end
   end
endmodule
