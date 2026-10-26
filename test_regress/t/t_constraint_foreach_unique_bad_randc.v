// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// No randc variable shall appear in a unique group (IEEE 1800-2023 18.5.4)

class RandcGrid;
  randc bit [4:0] grid[3][3];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i]};}
endclass

class RandcOneLeaf;
  randc bit [4:0] grid[3][1];
  constraint c1 {foreach (grid[i]) unique {grid[i]};}
endclass

class Inner;
  randc bit [4:0] val;
endclass

class RandcMemberScalar;
  rand Inner obj = new;
  constraint c1 {unique {obj.val};}
endclass

class RandcBareScalar;
  randc bit [4:0] x;
  constraint c1 {unique {x};}
endclass

module t;
  initial begin
    automatic RandcGrid rg = new;
    automatic RandcOneLeaf rol = new;
    automatic RandcMemberScalar rms = new;
    automatic RandcBareScalar rbs = new;
    void'(rg.randomize());
    void'(rol.randomize());
    void'(rms.randomize());
    void'(rbs.randomize());
  end
endmodule
