// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// Illegal unique groups (IEEE 1800-2023 18.5.4): a randc member, or a member
// whose leaf elements aren't integral or real.

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

typedef struct {rand bit [2:0] f;} unpacked_elem_s;
class UnpackedStructRows;
  rand unpacked_elem_s grid[2][3];
  constraint c {foreach (grid[i]) unique {grid[i]};}
endclass

class HandleElem;
  rand bit [2:0] f;
endclass
class HandleRows;
  rand HandleElem grid[2][3];
  constraint c {foreach (grid[i]) unique {grid[i]};}
endclass

class StringRows;
  rand bit unused;
  string grid[2][3];
  constraint c {foreach (grid[i]) unique {grid[i]};}
endclass

module t;
  initial begin
    automatic RandcGrid rg = new;
    automatic RandcOneLeaf rol = new;
    automatic RandcMemberScalar rms = new;
    automatic RandcBareScalar rbs = new;
    automatic UnpackedStructRows usr = new;
    automatic HandleRows hr = new;
    automatic StringRows sr = new;
    void'(rg.randomize());
    void'(rol.randomize());
    void'(rms.randomize());
    void'(rbs.randomize());
    void'(usr.randomize());
    void'(hr.randomize());
    void'(sr.randomize());
  end
endmodule
