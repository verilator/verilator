// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
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

// IEEE 1800-2023 18.7.1: m_x is in the list -> class scope.
// 'y' is NOT in the list -> must resolve in the caller scope (function arg = 10),
// not the class member 'y = -1'. If the restriction did not apply, the constraint
// 'm_x < y' would reduce to 'm_x < -1' which is unsatisfiable (m_x > 0).
function int func_restricted(Cls obj, int y);
  return obj.randomize() with (m_x) {
    m_x > 0;
    m_x < y;
  };
endfunction

// Multi-identifier list: both m_x and m_z bind into the class; 'lo' and 'hi' not
// in the list resolve to the caller arguments, even though 'lo' also exists as
// a class member.
function int func_multi(Cls obj, int lo, int hi);
  return obj.randomize() with (m_x, m_z) {
    m_x > lo;
    m_x < hi;
    m_z > lo;
    m_z < hi;
    m_x < m_z;
  };
endfunction

// Unrestricted form baseline: no identifier list, class scope first, then enclosing.
function int func_unrestricted(Cls obj);
  return obj.randomize() with {
    m_x > 0;
    m_x < 10;
  };
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
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
