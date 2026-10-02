// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit value;

  covergroup cg;
    cp_a: coverpoint value;
    cp_b: coverpoint value;
    other: cross cp_a, cp_b;
    cx: cross cp_a, cp_b{
      bins unknown = missing;
      bins wrong_cross = other;
      bins wrong_point = cp_a;
      bins invalid_left = missing && cx;
      bins invalid_right = cx || other;
    }
  endgroup

  int limit_value;

  covergroup cg_dynamic;
    cp_a: coverpoint value {
      ignore_bins ignored = {0};
    }
    cp_b: coverpoint value;
    cp_other: coverpoint value;
    other: cross cp_a, cp_b;
    cx: cross cp_a, cp_b{
      bins wrong_cross = other;
      bins invalid_left = missing && cx;
      bins invalid_right = cx || missing;
      bins wrong_point = binsof (cp_other);
      bins wrong_bin = binsof (cp_a.missing);
      bins duplicate = cx;
      bins duplicate = binsof (cp_b);
      bins nonconstant = binsof (cp_a) intersect {limit_value};
    }
  endgroup

  cg cov = new;
  cg_dynamic dynamic_cov = new;

  initial $finish;
endmodule
