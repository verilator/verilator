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
    xc: cross cp_a, cp_c {
      bins filtered = binsof(cp_a) intersect {0};
    }
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

  covergroup cgx_binsof;
    cp_a: coverpoint cp_expr {bins a = {0};}
    cp_b: coverpoint cp_expr {bins b = {0};}
    cp_other: coverpoint cp_expr {bins other = {0};}
    xc: cross cp_a, cp_b {
      bins missing_point = binsof(missing);
      bins uncrossed_point = binsof(cp_other);
      bins missing_bin = binsof(cp_a.missing);
      bins duplicate = binsof(cp_a);
      bins duplicate = binsof(cp_b);
      bins nonconstant = binsof(cp_a) intersect {size_var} || binsof(cp_b);
      bins nonconstant_range = binsof(cp_a) intersect {[0:size_var]};
    }
  endgroup

  covergroup cgx_binsof_large;
    cp_a: coverpoint cp_wide;
    cp_b: coverpoint cp_wide;
    cp_c: coverpoint cp_wide;
    cp_d: coverpoint cp_wide;
    cp_e: coverpoint cp_wide;
    cp_f: coverpoint cp_wide;
    xc: cross cp_a, cp_b, cp_c, cp_d, cp_e, cp_f {
      bins selected = binsof(cp_a);
    }
    auto_only: cross cp_a, cp_b, cp_c, cp_d, cp_e, cp_f;
  endgroup

  covergroup cgx_binsof_excluded;
    cp_a: coverpoint cp_expr {
      bins normal = {0};
      ignore_bins nonconstant = {size_var};
    }
    cp_b: coverpoint cp_expr {bins normal = {0};}
    xc: cross cp_a, cp_b {
      bins selected = binsof(cp_a) intersect {0};
    }
  endgroup

  logic [29:0] complex_value;
  localparam logic [29:0] ANY = 30'bx;

  covergroup cgx_binsof_complex;
    cp_a: coverpoint complex_value {
      bins whole = {[0:30'h3fffffff]};
      // Six pigeons in five holes: a deliberately hard union of excluded assignments.
      wildcard ignore_bins no_hole = {
        (ANY & ~30'h0000001f), (ANY & ~30'h000003e0), (ANY & ~30'h00007c00),
        (ANY & ~30'h000f8000), (ANY & ~30'h01f00000), (ANY & ~30'h3e000000)
      };
      wildcard ignore_bins shared_hole = {
        (ANY | 30'h00000021), (ANY | 30'h00000401), (ANY | 30'h00008001), (ANY | 30'h00100001),
        (ANY | 30'h02000001), (ANY | 30'h00000420), (ANY | 30'h00008020), (ANY | 30'h00100020),
        (ANY | 30'h02000020), (ANY | 30'h00008400), (ANY | 30'h00100400), (ANY | 30'h02000400),
        (ANY | 30'h00108000), (ANY | 30'h02008000), (ANY | 30'h02100000), (ANY | 30'h00000042),
        (ANY | 30'h00000802), (ANY | 30'h00010002), (ANY | 30'h00200002), (ANY | 30'h04000002),
        (ANY | 30'h00000840), (ANY | 30'h00010040), (ANY | 30'h00200040), (ANY | 30'h04000040),
        (ANY | 30'h00010800), (ANY | 30'h00200800), (ANY | 30'h04000800), (ANY | 30'h00210000),
        (ANY | 30'h04010000), (ANY | 30'h04200000), (ANY | 30'h00000084), (ANY | 30'h00001004),
        (ANY | 30'h00020004), (ANY | 30'h00400004), (ANY | 30'h08000004), (ANY | 30'h00001080),
        (ANY | 30'h00020080), (ANY | 30'h00400080), (ANY | 30'h08000080), (ANY | 30'h00021000),
        (ANY | 30'h00401000), (ANY | 30'h08001000), (ANY | 30'h00420000), (ANY | 30'h08020000),
        (ANY | 30'h08400000), (ANY | 30'h00000108), (ANY | 30'h00002008), (ANY | 30'h00040008),
        (ANY | 30'h00800008), (ANY | 30'h10000008), (ANY | 30'h00002100), (ANY | 30'h00040100),
        (ANY | 30'h00800100), (ANY | 30'h10000100), (ANY | 30'h00042000), (ANY | 30'h00802000),
        (ANY | 30'h10002000), (ANY | 30'h00840000), (ANY | 30'h10040000), (ANY | 30'h10800000),
        (ANY | 30'h00000210), (ANY | 30'h00004010), (ANY | 30'h00080010), (ANY | 30'h01000010),
        (ANY | 30'h20000010), (ANY | 30'h00004200), (ANY | 30'h00080200), (ANY | 30'h01000200),
        (ANY | 30'h20000200), (ANY | 30'h00084000), (ANY | 30'h01004000), (ANY | 30'h20004000),
        (ANY | 30'h01080000), (ANY | 30'h20080000), (ANY | 30'h21000000)
      };
    }
    cp_b: coverpoint cp_expr;
    xc: cross cp_a, cp_b {
      bins selected = binsof(cp_a.whole) intersect {[0:30'h3fffffff]} && binsof(cp_b);
    }
  endgroup

  covergroup cgx_binsof_many_values;
    cp_a: coverpoint cp_wide {
      bins whole[] = {[0:767]};
      // These singleton queries must not consume an aggregate nonlinear-search budget.
      wildcard ignore_bins removed = {
        16'b??1????11???????, 16'b?0????0??1??????, 16'b????1?1????????0, 16'b1??????1?1??????,
        16'b???????????0??10, 16'b???????0?????1?0, 16'b????1????1???0??, 16'b?1??0?????1?????,
        16'b??????0????0?0??, 16'b?????1?????00???, 16'b???????0??1?0???, 16'b????????0??0???0,
        16'b???????0??1????0, 16'b?0??1??????????0, 16'b0?????????0???1?, 16'b???????1????01??,
        16'b??0????????1???0, 16'b?1???????1??0???, 16'b?10??0??????????, 16'b10??????1???????,
        16'b1???????1????1??, 16'b1????????????1?0, 16'b??1????????01???, 16'b???1???0???????0,
        16'b1???????1?1?????, 16'b?10???0?????????, 16'b?1???1??1???????, 16'b10?0????????????,
        16'b?00???0?????????, 16'b????????10???1??, 16'b??????1????10???, 16'b??????01???????0,
        16'b???1????1???1???, 16'b???1????1??0????, 16'b???1?0????????1?, 16'b????0?0??0??????,
        16'b????1??0?????1??, 16'b??0??1????????1?, 16'b?????11????????1, 16'b????1?01????????,
        16'b?????0?00???????, 16'b???1????0????1??, 16'b?0????????0???1?, 16'b??????10??????0?,
        16'b1?0??0??????????, 16'b10?????0????????, 16'b10?0????????????, 16'b???10??????????0,
        16'b1????0????1?????, 16'b?0?????????1??0?, 16'b???0?????1?????0, 16'b?00???????0?????,
        16'b????0????1????0?, 16'b0????1??????1???, 16'b?1??1????0??????, 16'b???????0??????10,
        16'b?????0??01??????, 16'b?0???1?0????????, 16'b?1????1?1???????, 16'b?????00??0??????
      };
    }
    cp_b: coverpoint cp_expr;
    xc: cross cp_a, cp_b {
      bins selected = binsof(cp_a.whole) intersect {[0:16'hffff]};
    }
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
  cgx_binsof cgx_binsof_inst = new;
  cgx_binsof_large cgx_binsof_large_inst = new;
  cgx_binsof_excluded cgx_binsof_excluded_inst = new;
  cgx_binsof_complex cgx_binsof_complex_inst = new;
  cgx_binsof_many_values cgx_binsof_many_values_inst = new;

  initial $finish;
endmodule
