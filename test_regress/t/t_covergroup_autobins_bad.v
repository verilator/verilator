// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Tests for automatic bins error conditions

module t;
  int size_var;
  logic [3:0] cp_expr;

  // Error: array size must be a constant
  covergroup cg1;
    cp1: coverpoint cp_expr {
      bins auto[size_var];
    }
  endgroup

  // Error: array size must be >= 1 (zero)
  covergroup cg2;
    cp1: coverpoint cp_expr {
      bins auto[0];
    }
  endgroup

  // Error: array size exceeds limit of 1000
  covergroup cg2b;
    cp1: coverpoint cp_expr {
      bins auto[1001];
    }
  endgroup

  // Error: non-constant value in bin ranges
  covergroup cg3;
    cp1: coverpoint cp_expr {
      bins b[] = {[size_var:size_var]};  // non-constant array bins range (both bounds non-const)
      bins b_mixed[] = {[0:size_var]};   // non-constant array bins range (max bound non-const)
      bins b_range = {[size_var:4]};     // non-constant regular bin range (lhs non-const)
      bins b_range2 = {[0:size_var]};    // non-constant regular bin range (rhs non-const)
      bins b2 = {size_var};              // non-constant simple bin value
      ignore_bins ign = {size_var};      // non-constant ignore_bins value
      ignore_bins ign_range = {[0:size_var]};  // non-constant ignore_bins range (rhs non-const)
    }
  endgroup

  // Error: non-constant coverpoint option value
  covergroup cg4;
    cp1: coverpoint cp_expr {
      option.at_least = size_var;  // non-constant coverpoint option value
    }
  endgroup

  // Error: four-state (x/z) value in bin range bound, and non-constant lower bound
  covergroup cg5;
    cp1: coverpoint cp_expr {
      bins b_xz = {[4'bxxxx:4'hF]};                // four-state lower bound (match-code path)
      ignore_bins ign_xz_lo = {[4'bxxxx:4'hF]};    // four-state lower bound (range-enum path)
      ignore_bins ign_xz_hi = {[4'h0:4'bzzzz]};    // four-state upper bound (range-enum path)
      ignore_bins ign_nclo = {[size_var:4]};       // non-constant lower bound
      bins b_nc_ub = {[size_var:$]};                // non-constant lower bound, open-ended '$' upper
      bins b_xz_ub = {[4'bxxxx:$]};                 // four-state lower bound, open-ended '$' upper
    }
  endgroup

  cg1 cg1_inst = new;
  cg2 cg2_inst = new;
  cg2b cg2b_inst = new;
  cg3 cg3_inst = new;
  cg4 cg4_inst = new;
  cg5 cg5_inst = new;

  initial $finish;
endmodule
