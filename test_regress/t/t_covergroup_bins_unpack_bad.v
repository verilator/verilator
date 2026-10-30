// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int index;
  function automatic int existing_function();
    return 1;
  endfunction
  int bad_with = existing_function with (1);
  logic [3:0] cp_expr;

  covergroup cg with function sample (bit value);
    cp: coverpoint value {
      bins brace_lhs[] = {4'd1, 4'd2} == 8'h12;
      bins brace_select[] = {4'd1, 4'd2}[3:0];
      bins root_increment[] = ++index;
      bins brace_lhs_single[] = {4'd1} == 4'h1;
      bins brace_lhs_triple[] = {4'd1, 4'd2, 4'd3} == 12'h123;
      bins scalar_array[] = cp_expr;
    }
  endgroup

  cg cg_inst = new;
endmodule
