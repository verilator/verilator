// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module detail_code(
    input clk,
    input reset_l);
endmodule

module sub_top(
    input clk,
    input reset_l);

    detail_code u0(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u1(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u2(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u3(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u4(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u5(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u6(
          .clk(clk),
          .reset_l(reset_l)
    );
    detail_code u7(
          .clk(clk),
          .reset_l(reset_l)
    );
endmodule

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
