// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

class ArgCls;
  rand int b;
endclass

class Cls;
  rand int m_x;
  rand int m_z;
  int y = -1;  // class member named 'y' intentionally shadows the caller arg
  int lo = -100;  // class member named 'lo' intentionally shadows the caller arg
  rand int a[];

  function new();
    a = new[10];
  endfunction

  // Randomize array inside class that is argument
  // with .size inside if
  function automatic int randomize_subcls(ArgCls ac);
    return ac.randomize() with {
      if (a.size() > 0) {
        ac.b == a.size();
      }
    };
  endfunction
endclass

class Grid;
  rand bit [4:0] grid[3][3];
  rand int cube[2][3][4];
  rand int x;

  // A nested foreach with an omitted first dimension, randomized from a class method.
  function int randomize_self(int off);
    return randomize() with {
      foreach (cube[i]) {
        foreach (cube[, j, k]) cube[i][j][k] == i + j + k + off;
      }
    };
  endfunction
endclass

// Foreach loop variables are local; the caller arg 'k' is captured where no loop 'k' shadows it.
function automatic int func_foreach(Grid obj, int k);
  return obj.randomize() with {
    x == k;
    foreach (cube[i, j, k]) cube[i][j][k] == 100 * i + 10 * j + k;
  };
endfunction

// 'y' is not in the list -> resolves to the caller arg (10), not class member (-1).
function int func_restricted(Cls obj, int y);
  return obj.randomize() with (m_x) {
    m_x > 0;
    m_x < y;
  };
endfunction

// Multi-id list: 'lo' is also a class member but resolves to caller arg.
function int func_multi(Cls obj, int lo, int hi);
  return obj.randomize() with (m_x, m_z) {
    m_x > lo;
    m_x < hi;
    m_z > lo;
    m_z < hi;
    m_x < m_z;
  };
endfunction

// Unrestricted baseline: no id list.
function int func_unrestricted(Cls obj);
  return obj.randomize() with {
    m_x > 0;
    m_x < 10;
  };
endfunction

// Empty id list: no name binds into the class; constraint references obj.* explicitly.
function automatic int func_empty(Cls obj, int lo, int hi);
  // verilog_format: off
  return obj.randomize() with () {
    obj.m_x > lo;
    obj.m_x < hi;
  };
  // verilog_format: on
endfunction

// 'local::y' bypasses class scope -> caller arg, not obj.y.
function int func_local_qual(Cls obj, int y);
  obj.y = -42;
  // verilog_format: off
  return obj.randomize() with {
    m_x > 0;
    m_x < local::y;
  };
  // verilog_format: on
endfunction

// Consecutive restricted blocks must not leak each other's id list.
function automatic int func_sequential(Cls obj, int hi);
  int rc = 1;
  rc &= obj.randomize() with (m_x) { m_x > 0; m_x < hi; };
  rc &= obj.randomize() with (m_z) { m_z > 0; m_z < hi; };
  return rc;
endfunction

module t;
  initial begin
    Cls c;
    ArgCls ac;
    int i;
    c = new;
    ac = new;
    repeat (20) begin
      i = func_restricted(c, 10);
      `checkd(i, 1);
      `check_range(c.m_x, 1, 9);
      i = func_multi(c, 0, 50);
      `checkd(i, 1);
      `check_range(c.m_x, 1, 49);
      `check_range(c.m_z, 1, 49);
      `checkd(c.m_x < c.m_z, 1);
      i = func_unrestricted(c);
      `checkd(i, 1);
      `check_range(c.m_x, 1, 9);
      i = func_empty(c, 0, 9);
      `checkd(i, 1);
      `check_range(c.m_x, 1, 8);
      i = func_local_qual(c, 8);
      `checkd(i, 1);
      `check_range(c.m_x, 1, 7);
      i = func_sequential(c, 6);
      `checkd(i, 1);
      i = c.randomize_subcls(ac);
      `checkd(i, 1);
      if (c.a.size() > 0) begin
        `checkd(ac.b, c.a.size());
      end
      // Statement form: discards return value via void'.
      void'(c.randomize() with (m_x) { m_x > 0; m_x < 5; });
      `check_range(c.m_x, 1, 4);
    end
    begin
      automatic Grid g = new;
      automatic int m[2][3];
      automatic int ok;
      for (int n = 0; n < 20; ++n) begin
        void'(g.randomize() with {foreach (grid[i, j]) grid[i][j] inside {[1:9]};});
        foreach (g.grid[i, j]) `check_range(g.grid[i][j], 1, 9);
        ok = func_foreach(g, n);
        `checkd(ok, 1);
        `checkd(g.x, n);
        foreach (g.cube[i, j, k]) `checkd(g.cube[i][j][k], 100 * i + 10 * j + k);
        ok = g.randomize_self(n);
        `checkd(ok, 1);
        foreach (g.cube[i, j, k]) `checkd(g.cube[i][j][k], i + j + k + n);
        ok = std::randomize(m) with {foreach (m[i, j]) m[i][j] == 10 * i + j + n;};
        `checkd(ok, 1);
        foreach (m[i, j]) `checkd(m[i][j], 10 * i + j + n);
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
