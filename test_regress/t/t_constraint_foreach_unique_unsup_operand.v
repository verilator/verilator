// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// A unique{} sole item that isn't a variable, member, or constant-indexed
// slice (here, a function call). Lint-only, to capture the warning text.

typedef bit [4:0] row3_t[3];
class FuncItem;
  rand bit [4:0] grid[3][3];
  function row3_t get_row();
    return grid[0];
  endfunction
  constraint c1 {unique {get_row()};}
endclass

typedef struct {rand bit [2:0] r[4];} row_s;
class StructRows;
  rand row_s s[2];
  constraint c1 {foreach (s[i]) unique {s[i].r};}
endclass

class ContainerRows;
  rand bit [2:0] q[$][4];
  rand bit [2:0] a[int][4];
  constraint c1 {foreach (q[i]) unique {q[i]};}
  constraint c2 {foreach (a[i]) unique {a[i]};}
endclass

class StateRowAtRandIndex;
  rand int ri;
  bit [2:0] s[3][4];
  bit [2:0] s3[3][2][4];
  constraint c1 {ri inside {[0 : 2]}; unique {s[ri]};}
  constraint c2 {unique {s3[ri][1]};}
endclass

module t;
  initial begin
    automatic FuncItem fi = new;
    automatic StructRows sr = new;
    automatic ContainerRows cr = new;
    automatic StateRowAtRandIndex srri = new;
    void'(fi.randomize());
    void'(sr.randomize());
    void'(cr.randomize());
    void'(srri.randomize());
  end
endmodule
