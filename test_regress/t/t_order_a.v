// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_order_a (/*AUTOARG*/
   // Outputs
   m_from_clk_lev1_r, n_from_clk_lev2, o_from_com_levs11,
   o_from_comandclk_levs12,
   // Inputs
   clk, a_to_clk_levm3, b_to_clk_levm1, c_com_levs10, d_to_clk_levm2, one
   );

   input clk;
   input [7:0] a_to_clk_levm3;
   input [7:0] b_to_clk_levm1;
   input [7:0] c_com_levs10;
   input [7:0] d_to_clk_levm2;
   input [7:0] one;
   output [7:0] m_from_clk_lev1_r;
   output [7:0] n_from_clk_lev2;
   output [7:0] o_from_com_levs11;
   output [7:0] o_from_comandclk_levs12;

   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [7:0]            m_from_clk_lev1_r;
   // End of automatics

   // surefire lint_off ASWEBB
   // surefire lint_off ASWEMB

   wire [7:0] a_to_clk_levm1;
   wire [7:0] a_to_clk_levm2;
   wire [7:0] c_com_levs11;
   reg [7:0]  o_from_comandclk_levs12;
   wire [7:0]  n_from_clk_lev2;
   wire [7:0]  n_from_clk_lev3;

   assign     a_to_clk_levm1 = a_to_clk_levm2 + d_to_clk_levm2;
   assign     a_to_clk_levm2 = a_to_clk_levm3 + 0;

   always @ (posedge clk) begin
      m_from_clk_lev1_r <= a_to_clk_levm1 + b_to_clk_levm1;
   end

   assign c_com_levs11 = c_com_levs10 + one;
   always @ (/*AS*/c_com_levs11 or n_from_clk_lev3) o_from_comandclk_levs12 = c_com_levs11 + n_from_clk_lev3;
   assign n_from_clk_lev2 = m_from_clk_lev1_r;
   assign n_from_clk_lev3 = n_from_clk_lev2;
   wire [7:0] o_from_com_levs11 = c_com_levs10 + 1;

endmodule
