// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// No randc variable shall appear in a unique group (IEEE 1800-2023 18.5.4)

class RandcGrid;
  randc bit [4:0] grid[3][3];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i]};}
endclass

module t;
  initial begin
    automatic RandcGrid rg = new;
    void'(rg.randomize());
  end
endmodule
