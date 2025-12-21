// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic a2_i,
    a1_i,
    a0_i,
    input logic b_i,
    output logic d_o
);
  // verilator lint_off PINMISSING
  Sub sub (
      .a_i({a2_i, a1_i, a0_i}),
      .b_i,
      .d_o
  );
  // verilator lint_on PINMISSING
endmodule

module Sub (
    input logic [2:0] a_i,
    input logic b_i,
    output logic c_o,
    output logic d_o
);
  assign c_o = (a_i != 0) ? 1 : 0;
  assign d_o =  // Note = not == below
      (
      c_o = 1  // <--- Warning: ASSIGNEQEXPR
      ) ? 1 : (
      c_o = 0  // <--- Warning: ASSIGNEQEXPR
      ) ? b_i : 0;
endmodule
