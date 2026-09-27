// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit [3:0] value;
  real real_value;
  localparam string TEXT = "a";

  covergroup cg_values;
    cp: coverpoint value {
      bins text = {TEXT};
      bins text_array[] = {TEXT};
      bins text_sized[2] = {TEXT};
      ignore_bins ignored = {0};
    }
  endgroup

  // A sized array of bins with a non-integral bound given to the constructor, and of a real
  // coverpoint, which is treated as an array of a bin per value
  covergroup cg_sized(real lo);
    cp: coverpoint value {
      bins real_bound[2] = {[lo : 5]};
    }
    cp_real: coverpoint real_value {
      bins sized[2] = {1.0, 2.0};
    }
  endgroup

  covergroup cg_wild;
    cp: coverpoint value {
      wildcard bins text = {TEXT};
    }
  endgroup

  covergroup cg_transition;
    cp: coverpoint value {
      bins text = (1 => TEXT);
      ignore_bins ignored = {0};
    }
  endgroup

  covergroup cg_cross;
    cp_real: coverpoint real_value {
      bins one = {1.0};
    }
    cp_plain: coverpoint value;
    cp_dynamic: coverpoint value {
      ignore_bins ignored = {0};
    }
    static_cross: cross cp_real, cp_plain{bins selected = binsof (cp_real) intersect {1};}
    dynamic_cross: cross cp_real, cp_dynamic{bins selected = binsof (cp_real) intersect {1};}
  endgroup

  cg_values values_cov = new;
  cg_sized sized_cov = new(1.0);
  cg_wild wild_cov = new;
  cg_transition transition_cov = new;
  cg_cross cross_cov = new;

  initial $finish;
endmodule
