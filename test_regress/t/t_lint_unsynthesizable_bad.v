// DESCRIPTION: Verilator: Test of UNSYNTHESIZABLE warning on / % ** operators
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

module t (
  input wire [7:0] a, b,
  input wire signed [7:0] sa, sb,
  output wire [7:0] q_div,
  output wire [7:0] q_mod,
  output wire signed [7:0] q_divs,
  output wire signed [7:0] q_mods,
  output wire [15:0] q_pow
);
  assign q_div  = a / b;
  assign q_mod  = a % b;
  assign q_divs = sa / sb;
  assign q_mods = sa % sb;
  assign q_pow  = a ** b;
endmodule
