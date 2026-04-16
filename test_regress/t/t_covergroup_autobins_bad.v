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

  // Error: non-constant value in bin ranges
  covergroup cg3;
    cp1: coverpoint cp_expr {
      bins b[] = {[size_var:size_var]};  // non-constant array bins range (both bounds non-const)
      bins b_mixed[] = {[0:size_var]};   // non-constant array bins range (max bound non-const)
      bins b2 = {size_var};              // non-constant simple bin value
      ignore_bins ign = {size_var};      // non-constant ignore_bins value
    }
  endgroup

  // Error: non-constant coverpoint option value
  covergroup cg4;
    cp1: coverpoint cp_expr {
      option.at_least = size_var;  // non-constant coverpoint option value
    }
  endgroup

  cg1 cg1_inst = new;
  cg2 cg2_inst = new;
  cg3 cg3_inst = new;
  cg4 cg4_inst = new;

  initial $finish;
endmodule
