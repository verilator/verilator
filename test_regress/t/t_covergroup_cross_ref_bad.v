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

  cg cov = new;

  initial $finish;
endmodule
