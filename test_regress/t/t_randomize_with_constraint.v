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

class Cls;
  rand int m_x;
  rand int m_z;
  int y = -1;  // class member named 'y' intentionally shadows the caller arg
  int lo = -100;  // class member named 'lo' intentionally shadows the caller arg
endclass

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
    int i;
    c = new;
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
      // Statement form: discards return value via void'.
      void'(c.randomize() with (m_x) { m_x > 0; m_x < 5; });
      `check_range(c.m_x, 1, 4);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
