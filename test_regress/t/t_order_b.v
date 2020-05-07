// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_order_b (/*AUTOARG*/
   // Outputs
   o_subfrom_clk_lev2,
   // Inputs
   m_from_clk_lev1_r
   );

   input  [7:0] m_from_clk_lev1_r;
   output [7:0] o_subfrom_clk_lev2;

   wire [7:0] o_subfrom_clk_lev2 = m_from_clk_lev1_r;

endmodule
