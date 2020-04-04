// DESCRIPTION: Verilator: Verilog example module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

module top
  (
   input         clk,
   input         fastclk,
   input         reset_l,

   output wire [1:0]  out_small,
   output wire [39:0] out_quad,
   output wire [69:0] out_wide,
   input [1:0]   in_small,
   input [39:0]  in_quad,
   input [69:0]  in_wide
   );

   sub #(.TYPE_t(logic [1:0])) sub_small
     (.in(in_small),
      .out(out_small));

   sub #(.TYPE_t(logic [39:0])) sub_quad
     (.in(in_quad),
      .out(out_quad));

   sub #(.TYPE_t(logic [69:0])) sub_wide
     (.in(in_wide),
      .out(out_wide));
endmodule
