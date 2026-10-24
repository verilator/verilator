// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int size_var;
  logic [3:0] cp_expr;
  logic [31:0] cp_32bit;

  // Error: option.auto_bin_max must be a constant expression (group level)
  covergroup cg;
    option.auto_bin_max = size_var;
    cp: coverpoint cp_expr;
  endgroup

  // Warning (COVERIGN): more automatic bins than --coverage-max-bins (1024)
  covergroup cg_limit;
    option.auto_bin_max = 2000000;
    cp: coverpoint cp_32bit;
  endgroup

  // Warning (COVERIGN): non-constant option.at_least
  covergroup cg_at_least;
    option.at_least = size_var;
    cp: coverpoint cp_expr;
  endgroup

  // Warning (COVERIGN): negative option.at_least, at each level
  covergroup cg_at_least_neg;
    option.at_least = -1;
    cp_a: coverpoint cp_expr {option.at_least = -2;}
    cp_b: coverpoint cp_expr;
    cx: cross cp_a, cp_b{option.at_least = -3;}
  endgroup

  cg cg_i = new;
  cg_limit cg_limit_i = new;
  cg_at_least cg_at_least_i = new;
  cg_at_least_neg cg_at_least_neg_i = new;
  initial $finish;
endmodule
