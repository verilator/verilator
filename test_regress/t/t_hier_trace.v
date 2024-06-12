// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(
    input clk,
    input reset_l);

    sub_top u0_sub_top(
          .clk(clk),
          .reset_l(reset_l)
    );
    sub_top u1_sub_top(
          .clk(clk),
          .reset_l(reset_l)
    );

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
