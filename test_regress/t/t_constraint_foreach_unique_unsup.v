// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Unsupported shapes of unique{} over a foreach-indexed array slice: the
// constraint is ignored (with a warning), but randomize() should still
// succeed on the class's other constraints.

class Cube;
  rand bit [4:0] cube[2][3][3];
  constraint c1 {foreach (cube[i]) unique {cube[i]};}
endclass

class WideRows;
  rand bit [7:0] wide[2][101];
  constraint c1 {foreach (wide[i]) unique {wide[i]};}
endclass

// A scalar alongside an array in the same group still needs its own
// unsupported warning -- distinct from unique{x} alone (a sole item,
// trivially unique, no warning at all).
class ScalarAndArray;
  rand bit [3:0] x;
  rand bit [3:0] arr[4];
  constraint c1 {unique {x, arr};}
endclass

// A sole item that isn't a variable, member, or constant-indexed slice at
// all (here, a function call) can't be safely cloned per element -- must
// be diagnosed directly rather than silently accepted.
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
    automatic Cube cb = new;
    automatic WideRows wr = new;
    automatic ScalarAndArray sa = new;
    automatic FuncItem fi = new;
    int ok;
    repeat (20) begin
      ok = cb.randomize();
      `checkd(ok, 1)
      ok = wr.randomize();
      `checkd(ok, 1)
      ok = sa.randomize();
      `checkd(ok, 1)
      ok = fi.randomize();
      `checkd(ok, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
