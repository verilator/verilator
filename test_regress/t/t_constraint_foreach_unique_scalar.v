// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// unique{} on a single scalar element inside a foreach (as opposed to a
// whole row) is a vacuously-true one-element set. Previously crashed the
// compiler the same way an unsupported array-typed slice did. A
// foreach-indexed row of size 1 is the same case in array-slice form.

class Grid;
  rand bit [4:0] grid[3][3];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i][0]};}
endclass

class Row1;
  rand bit [4:0] grid[3][1];
  constraint c1 {foreach (grid[i]) unique {grid[i]};}
endclass

module t;
  initial begin
    automatic Grid g = new;
    automatic Row1 r = new;
    int ok;
    repeat (20) begin
      ok = g.randomize();
      `checkd(ok, 1)
      ok = r.randomize();
      `checkd(ok, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
