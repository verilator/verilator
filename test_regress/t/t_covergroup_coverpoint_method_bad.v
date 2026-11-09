// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test a coverpoint named other than as the prefix of a hierarchical name, and a method a
// coverpoint does not have (IEEE 1800-2023 19.5, 19.8)

module t;
  int a;
  real r;

  covergroup cg;
    cp: coverpoint a;
  endgroup

  cg cg_i = new;

  initial begin
    r = cg_i.cp;  // <--- Bad: not a prefix
    cg_i.cp.sample();  // <--- Bad: a method of a covergroup only
  end
endmodule
