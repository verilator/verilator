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
  logic [15:0] cp_wide;

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
      bins b_mixed[] = {[0:size_var]};  // non-constant array bins range (max bound non-const)
      bins b_range = {[size_var:4]};  // non-constant regular bin range (lhs non-const)
      bins b_range2 = {[0:size_var]}; // non-constant regular bin range (rhs non-const)
      bins b2 = {size_var};  // non-constant simple bin value
      ignore_bins ign = {size_var};  // non-constant ignore_bins value
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
      bins b_xz = {[4'bxxxx:4'hF]};  // four-state lower bound (match-code path)
      ignore_bins ign_xz_lo = {[4'bxxxx:4'hF]};  // four-state lower bound (range-enum path)
      ignore_bins ign_xz_hi = {[4'h0:4'bzzzz]};  // four-state upper bound (range-enum path)
      ignore_bins ign_nclo = {[size_var:4]};  // non-constant lower bound
      bins b_nc_ub = {[size_var:$]};  // non-constant lower bound, open-ended '$' upper
      bins b_xz_ub = {[4'bxxxx:$]};  // four-state lower bound, open-ended '$' upper
      bins b_xz_arr[] = {[4'bxxxx:4'hF]};  // four-state lower bound (array-bins path)
      bins b_xz_arr_hi[] = {[4'h0:4'bzzzz]};  // four-state upper bound (array-bins path)
    }
  endgroup

  // Warning (COVERIGN): array bins range exceeds COVER_BINS_LIMIT
  covergroup cg6;
    cp1: coverpoint cp_wide {
      bins b_huge[] = {[0:$]};  // open '[lo:$]' over 16-bit coverpoint exceeds bin limit
    }
  endgroup

  // Malformed bins on a coverpoint that feeds a *cross*.  The cross path
  // sizes the coverpoint's hit list (computeHitListBound/extractRangeIntervals)
  // before the bin condition is built, so the malformed-bin guards there run gracefully and
  // the user error is then diagnosed downstream by the bin-condition / array-value builders.
  // (Without a cross the same errors fire via cg3/cg5 above; the cross also exercises the
  // hit-list-sizing guard path.)
  covergroup cgx_nc_value;  // non-constant value, non-array bin
    cp_a: coverpoint cp_expr {bins x = {size_var};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup
  covergroup cgx_nc_range_lo;  // non-constant low bound, non-array range
    cp_a: coverpoint cp_expr {bins x = {[size_var : 1]};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup
  covergroup cgx_nc_range_hi;  // non-constant high bound, non-array range
    cp_a: coverpoint cp_expr {bins x = {[0 : size_var]};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup
  covergroup cgx_arr_4state_lo;  // four-state low bound, array range
    cp_a: coverpoint cp_expr {bins x[] = {[4'b000x : 4'hF]};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup
  covergroup cgx_arr_4state_hi;  // four-state high bound, array range
    cp_a: coverpoint cp_expr {bins x[] = {[4'h0 : 4'b000x]};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup
  covergroup cgx_arr_ncval;  // non-constant value, array value list
    cp_a: coverpoint cp_expr {bins x[] = {size_var};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup
  covergroup cgx_arr_open;  // open-ended ('$') bounds, array range
    cp_a: coverpoint cp_expr {bins x[] = {[2 : $], [$ : 1]};}
    cp_c: coverpoint cp_expr {bins r = {0}; bins w = {1};}
    xc: cross cp_a, cp_c;
  endgroup

  cg1 cg1_inst = new;
  cg2 cg2_inst = new;
  cg2b cg2b_inst = new;
  cg3 cg3_inst = new;
  cg4 cg4_inst = new;
  cg5 cg5_inst = new;
  cg6 cg6_inst = new;
  cgx_nc_value cgx_nc_value_inst = new;
  cgx_nc_range_lo cgx_nc_range_lo_inst = new;
  cgx_nc_range_hi cgx_nc_range_hi_inst = new;
  cgx_arr_4state_lo cgx_arr_4state_lo_inst = new;
  cgx_arr_4state_hi cgx_arr_4state_hi_inst = new;
  cgx_arr_ncval cgx_arr_ncval_inst = new;
  cgx_arr_open cgx_arr_open_inst = new;

  initial $finish;
endmodule
