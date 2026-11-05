// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// unique{} on a single-leaf slice, scalar or array, is vacuously true.

class Grid;
  rand bit [4:0] grid[3][3];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i][0]};}
endclass

class Row1;
  rand bit [4:0] grid[3][1];
  constraint c1 {foreach (grid[i]) unique {grid[i]};}
endclass

class Row1x1;
  rand bit [4:0] cube[3][1][1];
  constraint c1 {foreach (cube[i]) unique {cube[i]};}
endclass

class BareScalar;
  rand bit [4:0] x;
  constraint c1 {unique {x};}
endclass

class Inner;
  rand bit [4:0] val;
endclass

class MemberScalar;
  rand Inner obj = new;
  constraint c1 {unique {obj.val};}
endclass

module t;
  initial begin
    automatic Grid g = new;
    automatic Row1 r = new;
    automatic Row1x1 r11 = new;
    automatic BareScalar bs = new;
    automatic MemberScalar ms = new;
    int ok;
    repeat (20) begin
      ok = g.randomize();
      `checkd(ok, 1)
      ok = r.randomize();
      `checkd(ok, 1)
      ok = r11.randomize();
      `checkd(ok, 1)
      ok = bs.randomize();
      `checkd(ok, 1)
      ok = ms.randomize();
      `checkd(ok, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
