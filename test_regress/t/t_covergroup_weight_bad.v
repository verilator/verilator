// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Invalid coverage weights (IEEE 1800-2023 19.7, 19.7.1)

module t;
  bit [1:0] a;

  covergroup cg_negative;
    option.weight = -1;  // <--- Bad: negative
    type_option.weight = -2;  // <--- Bad: negative
    cpa: coverpoint a {
      option.weight = -3;  // <--- Bad: negative
    }
    cpb: coverpoint a {
      type_option.weight = -4;  // <--- Bad: negative
    }
    x: cross cpa, cpb{option.weight = 2 - 7;}  // <--- Bad: negative
  endgroup

  covergroup cg_nonconst(int w);
    option.weight = w;  // ok
    type_option.weight = w;  // <--- Bad: not constant
    cpa: coverpoint a {
      type_option.weight = w;  // <--- Bad: not constant
    }
  endgroup

  cg_negative cg_negative_inst = new;
  cg_nonconst cg_nonconst_inst = new(1);
  initial $finish;
endmodule
