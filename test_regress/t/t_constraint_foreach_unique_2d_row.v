// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test unique{} applied to a row of a 2D array inside a foreach, e.g.
// foreach (grid[i]) unique {grid[i]}, and its SliceSel/randc-index variants.

class Grid;
  rand bit [4:0] grid[3][3];

  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (grid[i]) unique {grid[i]};}

  function void rows_are_unique();
    for (int r = 0; r < 3; r++) begin
      for (int x = 0; x < 3; x++) begin
        for (int y = x + 1; y < 3; y++) begin
          `checkd(grid[r][x] == grid[r][y], 0)
        end
      end
    end
  endfunction
endclass

class RandcSelIndex;
  randc bit [1:0] sel;
  rand bit [4:0] grid[3][3];

  constraint c_sel {sel inside {[0 : 2]};}
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {unique {grid[sel]};}

  function void sel_row_is_unique();
    for (int x = 0; x < 3; x++) begin
      for (int y = x + 1; y < 3; y++) begin
        `checkd(grid[sel][x] == grid[sel][y], 0)
      end
    end
  endfunction
endclass

class SliceRange;
  rand bit [1:0] a[3:0];
  constraint all_unique {unique {a};}
  constraint uniq {unique {a[2:1]};}
endclass

class SliceRangeAscending;
  rand bit [1:0] a[1:4];
  constraint all_unique {unique {a};}
  constraint uniq {unique {a[2:3]};}
endclass

class Inner;
  rand bit [4:0] grid[3][3];
endclass

class MemberRow;
  rand Inner obj = new;
  constraint c1 {foreach (obj.grid[i, j]) obj.grid[i][j] inside {[1 : 9]};}
  constraint c2 {foreach (obj.grid[i]) unique {obj.grid[i]};}

  function void rows_are_unique();
    for (int r = 0; r < 3; r++) begin
      for (int x = 0; x < 3; x++) begin
        for (int y = x + 1; y < 3; y++) begin
          `checkd(obj.grid[r][x] == obj.grid[r][y], 0)
        end
      end
    end
  endfunction
endclass

class ArraySliceFirst;
  rand bit [4:0] grid[3][3];
  rand bit [3:0] arr[4];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {unique {grid[0], arr};}

  function void arr_is_unique();
    for (int x = 0; x < 4; x++) begin
      for (int y = x + 1; y < 4; y++) begin
        `checkd(arr[x] == arr[y], 0)
      end
    end
  endfunction
endclass

class ArraySliceSecond;
  rand bit [4:0] grid[3][3];
  rand bit [3:0] arr[4];
  constraint c1 {foreach (grid[i, j]) grid[i][j] inside {[1 : 9]};}
  constraint c2 {unique {arr, grid[0]};}

  function void arr_is_unique();
    for (int x = 0; x < 4; x++) begin
      for (int y = x + 1; y < 4; y++) begin
        `checkd(arr[x] == arr[y], 0)
      end
    end
  endfunction
endclass

class GuardedRow;
  rand bit en;
  rand bit [1:0] grid[2][4];
  constraint c {foreach (grid[i]) if (en) unique {grid[i]};}

  function void rows_are_unique();
    for (int r = 0; r < 2; r++) begin
      for (int x = 0; x < 4; x++) begin
        for (int y = x + 1; y < 4; y++) begin
          `checkd(grid[r][x] == grid[r][y], 0)
        end
      end
    end
  endfunction
endclass

class ImpliedRow;
  rand bit [1:0] grid[2][4];
  constraint c {foreach (grid[i]) (i == 1) -> unique {grid[i]};}
endclass

class StateRows;
  rand bit dummy;
  bit [1:0] grid[2][3];
  constraint c {foreach (grid[i]) unique {grid[i]};}
endclass

module t;
  initial begin
    Grid g;
    RandcSelIndex rsi;
    SliceRange sr;
    SliceRangeAscending sra;
    MemberRow mr;
    ArraySliceFirst asf;
    ArraySliceSecond ass;
    GuardedRow gr;
    ImpliedRow ir;
    StateRows st;
    int i;
    g = new();
    rsi = new();
    sr = new();
    sra = new();
    mr = new();
    asf = new();
    ass = new();
    gr = new();
    ir = new();
    st = new();
    repeat (20) begin
      i = g.randomize();
      `checkd(i, 1)
      g.rows_are_unique();

      i = rsi.randomize();
      `checkd(i, 1)
      rsi.sel_row_is_unique();

      i = sr.randomize();
      `checkd(i, 1)
      `checkd(sr.a[2] == sr.a[1], 0)

      i = sra.randomize();
      `checkd(i, 1)
      `checkd(sra.a[2] == sra.a[3], 0)

      i = mr.randomize();
      `checkd(i, 1)
      mr.rows_are_unique();

      i = asf.randomize();
      `checkd(i, 1)
      asf.arr_is_unique();

      i = ass.randomize();
      `checkd(i, 1)
      ass.arr_is_unique();

      i = gr.randomize() with {en == 1;};
      `checkd(i, 1)
      gr.rows_are_unique();
      i = gr.randomize() with {en == 0;};
      `checkd(i, 1)

      i = ir.randomize();
      `checkd(i, 1)
      for (int x = 0; x < 4; x++) begin
        for (int y = x + 1; y < 4; y++) begin
          `checkd(ir.grid[1][x] == ir.grid[1][y], 0)
        end
      end
    end

    st.grid = '{'{0, 1, 2}, '{3, 1, 2}};
    i = st.randomize();
    `checkd(i, 1)
    st.grid[1][0] = 1;
    i = st.randomize();
    `checkd(i, 0)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
