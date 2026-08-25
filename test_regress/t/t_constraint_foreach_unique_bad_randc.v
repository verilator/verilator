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

// A randc slice with exactly one leaf element is still illegal -- must not
// be waved through by the same leaf-count check that makes a non-randc
// single-leaf slice a no-op.
class RandcOneLeaf;
  randc bit [4:0] grid[3][1];
  constraint c1 {foreach (grid[i]) unique {grid[i]};}
endclass

// A randc scalar reached through a class handle (AstMemberSel). Its own
// randc-ness must still be caught, not skipped because the root resolver
// can't see through the class handle.
class Inner;
  randc bit [4:0] val;
endclass

class RandcMemberScalar;
  rand Inner obj = new;
  constraint c1 {unique {obj.val};}
endclass

// A bare randc scalar, no array or class handle involved -- the randc
// counterpart of BareScalar in t_constraint_foreach_unique_scalar.v.
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
