// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: single-step transitions and unsupported repetition

module t;
  logic [3:0] cp_expr;

  covergroup cg;
    cp1: coverpoint cp_expr {
      bins t_double = (1, 2);  // Error: requires at least two values
      bins t_repeat = (1 [* 2]);  // Error: unsupported repetition operator
    }
  endgroup

  cg cg_inst = new;
  initial $finish;
endmodule
