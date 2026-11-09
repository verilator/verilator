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

typedef enum bit [2:0] {RE0, RE1, RE2, RE3, RE4} row_e;
typedef struct packed { bit [1:0] x; bit y; } row_ps;
class ElemRows;
  rand int gi[2][4];
  rand byte gb[2][4];
  rand row_e ge[2][4];
  rand row_ps gp[2][4];
  rand bit [70:0] gw[2][4];
  rand logic [2:0] gl[2][4];
  constraint c {
    foreach (gi[i]) unique {gi[i]};
    foreach (gb[i]) unique {gb[i]};
    foreach (ge[i]) unique {ge[i]};
    foreach (gp[i]) unique {gp[i]};
    foreach (gw[i]) unique {gw[i]};
    foreach (gl[i]) unique {gl[i]};
  }
endclass

class PigeonRows;
  rand bit [1:0] grid[2][5];
  constraint c {foreach (grid[i]) unique {grid[i]};}
endclass

class RangeRows;
  rand bit [2:0] gd[1:0][3:0];
  rand bit [2:0] gn[2:3][5:8];
  constraint c {foreach (gd[i]) unique {gd[i]}; foreach (gn[i]) unique {gn[i]};}
endclass

class ConstRowAndParts;
  rand bit [2:0] grid[3][4];
  rand bit [2:0] a[8];
  rand bit [2:0] b[8];
  constraint c {unique {grid[1]}; unique {a[2+:4]}; unique {b[5-:4]};}
endclass

class Rows3d;
  rand bit [2:0] cube[2][2][4];
  constraint c {foreach (cube[i, j]) unique {cube[i][j]};}
endclass

class CtxRows;
  rand bit en;
  rand bit z;
  rand bit [2:0] ge[2][4];
  rand bit [2:0] gn[2][4];
  rand bit [2:0] go[2][4];
  rand bit [2:0] gp[2][4];
  constraint c_en {en == 0; z == 1;}
  constraint c_else {foreach (ge[i]) if (en) ge[i][0] == 0; else unique {ge[i]};}
  constraint c_nested {foreach (gn[i]) if (!en) { if (z) unique {gn[i]}; }}
  constraint c_outer {if (!en) { foreach (go[i]) unique {go[i]}; }}
  constraint c_pinned {foreach (gp[i]) unique {gp[i]}; gp[0][0] == 7; gp[1][3] == 0;
                       unique {gp[0][1], gp[1][1]};}
endclass

class ModeRows;
  rand bit [1:0] grid[2][5];
  constraint u {foreach (grid[i]) unique {grid[i]};}
endclass

class InlineRows;
  rand bit [2:0] grid[2][4];
endclass

class ModeStateRows;
  rand bit [2:0] grid[2][3];
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
    ElemRows er;
    PigeonRows pr;
    RangeRows rr;
    ConstRowAndParts cp;
    Rows3d r3;
    CtxRows cr;
    ModeRows mr2;
    InlineRows inr;
    ModeStateRows msr;
    bit [2:0] sgrid[2][4];
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

    er = new;
    rr = new;
    cp = new;
    r3 = new;
    cr = new;
    repeat (20) begin
      i = er.randomize();
      `checkd(i, 1)
      for (int r = 0; r < 2; r++) begin
        for (int x = 0; x < 4; x++) begin
          for (int y = x + 1; y < 4; y++) begin
            `checkd(er.gi[r][x] == er.gi[r][y], 0)
            `checkd(er.gb[r][x] == er.gb[r][y], 0)
            `checkd(er.ge[r][x] == er.ge[r][y], 0)
            `checkd(er.gp[r][x] == er.gp[r][y], 0)
            `checkd(er.gw[r][x] == er.gw[r][y], 0)
            `checkd(er.gl[r][x] == er.gl[r][y], 0)
          end
        end
      end

      i = rr.randomize();
      `checkd(i, 1)
      for (int r = 0; r < 2; r++) begin
        for (int x = 0; x < 4; x++) begin
          for (int y = x + 1; y < 4; y++) begin
            `checkd(rr.gd[r][x] == rr.gd[r][y], 0)
            `checkd(rr.gn[r + 2][x + 5] == rr.gn[r + 2][y + 5], 0)
          end
        end
      end

      i = cp.randomize();
      `checkd(i, 1)
      for (int x = 0; x < 4; x++) begin
        for (int y = x + 1; y < 4; y++) begin
          `checkd(cp.grid[1][x] == cp.grid[1][y], 0)
          `checkd(cp.a[2 + x] == cp.a[2 + y], 0)
          `checkd(cp.b[2 + x] == cp.b[2 + y], 0)
        end
      end

      i = r3.randomize();
      `checkd(i, 1)
      for (int p = 0; p < 2; p++) begin
        for (int q = 0; q < 2; q++) begin
          for (int x = 0; x < 4; x++) begin
            for (int y = x + 1; y < 4; y++) begin
              `checkd(r3.cube[p][q][x] == r3.cube[p][q][y], 0)
            end
          end
        end
      end

      i = cr.randomize();
      `checkd(i, 1)
      `checkd(cr.gp[0][0], 7)
      `checkd(cr.gp[1][3], 0)
      `checkd(cr.gp[0][1] == cr.gp[1][1], 0)
      for (int r = 0; r < 2; r++) begin
        for (int x = 0; x < 4; x++) begin
          for (int y = x + 1; y < 4; y++) begin
            `checkd(cr.ge[r][x] == cr.ge[r][y], 0)
            `checkd(cr.gn[r][x] == cr.gn[r][y], 0)
            `checkd(cr.go[r][x] == cr.go[r][y], 0)
            `checkd(cr.gp[r][x] == cr.gp[r][y], 0)
          end
        end
      end
    end

    pr = new;
    i = pr.randomize();
    `checkd(i, 0)

    mr2 = new;
    mr2.u.constraint_mode(0);
    i = mr2.randomize();
    `checkd(i, 1)
    mr2.u.constraint_mode(1);
    i = mr2.randomize();
    `checkd(i, 0)

    inr = new;
    repeat (20) begin
      i = inr.randomize() with {foreach (grid[r]) unique {grid[r]};};
      `checkd(i, 1)
      for (int r = 0; r < 2; r++) begin
        for (int x = 0; x < 4; x++) begin
          for (int y = x + 1; y < 4; y++) begin
            `checkd(inr.grid[r][x] == inr.grid[r][y], 0)
          end
        end
      end
    end

    repeat (20) begin
      i = std::randomize(sgrid) with {foreach (sgrid[r]) unique {sgrid[r]};};
      `checkd(i, 1)
      for (int r = 0; r < 2; r++) begin
        for (int x = 0; x < 4; x++) begin
          for (int y = x + 1; y < 4; y++) begin
            `checkd(sgrid[r][x] == sgrid[r][y], 0)
          end
        end
      end
    end

    msr = new;
    msr.grid = '{'{0, 1, 2}, '{3, 4, 5}};
    msr.grid.rand_mode(0);
    i = msr.randomize();
    `checkd(i, 1)
    msr.grid[1][2] = 4;
    i = msr.randomize();
    `checkd(i, 0)

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
