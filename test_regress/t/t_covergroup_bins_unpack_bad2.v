// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Test: scalar set expressions

module t;
  logic [3:0] cp_expr;
  int scalar_value;

  covergroup cg;
    cp1: coverpoint cp_expr {
      bins t_single = (scalar_value);  // Error: a set expression must evaluate to an array
    }
  endgroup

  covergroup cg_scalars;
    cp: coverpoint cp_expr {
      ignore_bins scalar_ignore = (scalar_value);
      illegal_bins scalar_illegal[2] = (scalar_value);
      bins real_value = (1.5);
      bins string_value = string'("one");
      wildcard bins wildcard_scalar = (1'b1);
      wildcard ignore_bins wildcard_scalar_ignore[] = (1'b0);
      wildcard illegal_bins wildcard_scalar_illegal[2] = (1'b1);
    }
  endgroup
  cg_scalars scalar_inst = new;

  cg cg_inst = new;
  initial $finish;
endmodule
