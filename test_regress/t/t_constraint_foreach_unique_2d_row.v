// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Regression test: unique{} applied to a row (slice) of a 2D array inside a
// foreach, e.g. foreach (grid[i]) unique {grid[i]}. This previously caused
// an internal fault during --binary constraint-solver codegen (a foreach
// body fully consumed by AstConstraintUnique's own visit, with nothing left
// to unlink). It then, after an unrelated upstream fix changed unique{}
// lowering to also recurse into foreach bodies, regressed to a different but
// still-broken internal error ("constraint foreach without a body"), because
// a single-item range list was unconditionally treated as a vacuous
// one-element set even when that single item was itself an array (a row
// with multiple elements needing real pairwise distinctness).
//
// Runs many iterations because constraint solving is randomized per call;
// a single passing trial would not catch a solver that only sometimes
// enforces distinctness.

class Grid;
  rand bit [4:0] grid[3][3];

  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i]};}

  function bit rows_are_unique();
    for (int r = 0; r < 3; r++) begin
      for (int x = 0; x < 3; x++) begin
        for (int y = x + 1; y < 3; y++) begin
          if (grid[r][x] == grid[r][y]) return 0;
        end
      end
    end
    return 1;
  endfunction
endclass

module t;
  initial begin
    Grid g;
    g = new();
    repeat (500) begin
      `checkd(g.randomize(), 1)
      `checkd(g.rows_are_unique(), 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
