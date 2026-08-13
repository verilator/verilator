// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unsupported shapes of unique{} over a foreach-indexed array slice. These
// must be reported and skipped, not silently accepted (wrong) or left to
// crash the compiler (a foreach body with nothing left in it after an
// unsupported unique{} is dropped is its own separate failure mode).

class RandcGrid;
  randc bit [4:0] grid[3][3];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  // No randc variable shall appear in a uniqueness group (IEEE 1800-2023 18.5.4)
  constraint c2 {foreach (grid[i]) unique {grid[i]};}
endclass

class Cube;
  rand bit [4:0] cube[2][3][3];
  // A row of a 3-D array is itself a 2-D slice, not the 1-D slice this path supports
  constraint c1 {foreach (cube[i]) unique {cube[i]};}
endclass

module t;
  initial begin
    automatic RandcGrid rg = new;
    automatic Cube cb = new;
    void'(rg.randomize());
    void'(cb.randomize());
  end
endmodule
