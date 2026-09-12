// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// A unique{} sole item that isn't a variable, member, or constant-indexed
// slice (here, a function call). Kept separate from
// t_constraint_foreach_unique_unsup.v (execute-mode, proves randomize()
// still succeeds) so the exact warning text is captured for
// t_dist_warn_coverage.

typedef bit [4:0] row3_t[3];
class FuncItem;
  rand bit [4:0] grid[3][3];
  function row3_t get_row();
    return grid[0];
  endfunction
  constraint c1 {unique {get_row()};}
endclass

module t;
  initial begin
    automatic FuncItem fi = new;
    void'(fi.randomize());
  end
endmodule
