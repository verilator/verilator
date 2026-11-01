// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Test: scalar set expressions

module t;
  logic [3:0] cp_expr;

  covergroup cg;
    cp1: coverpoint cp_expr {
      bins t_single = (1);  // Error: a set expression must evaluate to an unpacked array
    }
  endgroup

  logic [1:0][3:0] packed_values;
  covergroup cg_scalars;
    cp: coverpoint cp_expr {
      ignore_bins scalar_ignore = (2);
      illegal_bins scalar_illegal[2] = (3);
      wildcard bins scalar_wild = (4);
      wildcard ignore_bins scalar_wild_ignore[] = (5);
      wildcard illegal_bins scalar_wild_illegal[2] = (6);
      bins packed_array[] = packed_values;
      bins real_value = (1.5);
      bins string_value = string'("one");
    }
  endgroup
  cg_scalars scalar_inst = new;

  cg cg_inst = new;
  initial $finish;
endmodule
