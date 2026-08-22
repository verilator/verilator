// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test unique{} applied to a row of a 2D array inside a foreach, e.g.
// foreach (grid[i]) unique {grid[i]}. Previously crashed the compiler.
// Repeats many times since constraint solving is randomized per call.

class Grid;
  rand bit [4:0] grid[3][3];

  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i]};}

  function void rows_are_unique();
    for (int r = 0; r < 3; r++) begin
      for (int x = 0; x < 3; x++) begin
        for (int y = x + 1; y < 3; y++) begin
          `checkd(grid[r][x] == grid[r][y], 0)
        end
      end
    end
  endfunction
endclass

// unique{} on a single slice selected by an index that is itself randc,
// where the array being selected from is not. Only the array's own
// randc-ness matters for the IEEE 1800-2023 18.5.4 check -- the index
// expression choosing *which* row is a different variable entirely, and
// its randc-ness must not be mistaken for the array's.
class RandcSelIndex;
  randc bit [1:0] sel;
  rand bit [4:0] grid[3][3];

  constraint c_sel {sel inside {[0 : 2]};}
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {unique {grid[sel]};}

  function void sel_row_is_unique();
    for (int x = 0; x < 3; x++) begin
      for (int y = x + 1; y < 3; y++) begin
        `checkd(grid[sel][x] == grid[sel][y], 0)
      end
    end
  endfunction
endclass

module t;
  initial begin
    Grid g;
    RandcSelIndex rsi;
    int i;
    g = new();
    rsi = new();
    repeat (500) begin
      i = g.randomize();
      `checkd(i, 1)
      g.rows_are_unique();

      i = rsi.randomize();
      `checkd(i, 1)
      rsi.sel_row_is_unique();
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
