// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class Inner;
  rand int m_val;
  constraint c_local { m_val inside {[1:5]}; }
  function new(); m_val = 0; endfunction
endclass

class Mid;
  int m_limit;
  rand int m_x;
  rand Inner m_inner;
  constraint c_mid { m_x == m_limit; }
  function new(int lim);
    m_limit = lim;
    m_inner = new();
  endfunction
endclass

class Top;
  rand Mid m_m1;
  rand Mid m_m2;
  rand int m_y;

  constraint c_global {
    m_m1.m_inner.m_val < m_m2.m_inner.m_val;
    m_y > m_m1.m_x;
    m_y < m_m2.m_x;
    m_m1.m_inner.m_val + m_m2.m_inner.m_val < 8;
  }

  function new();
    m_m1 = new(3);
    m_m2 = new(5);
    m_y = 0;
  endfunction
endclass

module t_constraint_global_random;
  int success;
  Top t;

  initial begin
    t = new();

    // Test 1: Regular randomize() with global constraints
    success = t.randomize();
    if (success != 1) $stop;

    // $display("m1.x=%0d, m2.x=%0d, y=%0d", t.m_m1.m_x, t.m_m2.m_x, t.m_y);
    // $display("m1.inner.val=%0d, m2.inner.val=%0d", t.m_m1.m_inner.m_val, t.m_m2.m_inner.m_val);

    if (t.m_m1.m_x != 3 || t.m_m2.m_x != 5) $stop;
    if (t.m_m1.m_inner.m_val >= t.m_m2.m_inner.m_val) $stop;
    if (t.m_y <= t.m_m1.m_x || t.m_y >= t.m_m2.m_x) $stop;
    if (t.m_m1.m_inner.m_val + t.m_m2.m_inner.m_val >= 8) $stop;
    if (t.m_m1.m_inner.m_val < 1 || t.m_m1.m_inner.m_val > 5 ||
        t.m_m2.m_inner.m_val < 1 || t.m_m2.m_inner.m_val > 5) $stop;

    // Test 2: randomize() with inline constraint on global-constrained members
    success = 0;
    success = t.randomize() with {
      m_m1.m_inner.m_val == 2;
      m_m2.m_inner.m_val == 5;
    };
    if (success != 1) $stop;

    // Verify inline constraints
    if (t.m_m1.m_inner.m_val != 2) $stop;
    if (t.m_m2.m_inner.m_val != 5) $stop;

    // Verify global constraints still hold
    if (t.m_m1.m_x != 3 || t.m_m2.m_x != 5) $stop;
    if (t.m_m1.m_inner.m_val >= t.m_m2.m_inner.m_val) $stop;
    if (t.m_y <= t.m_m1.m_x || t.m_y >= t.m_m2.m_x) $stop;
    if (t.m_m1.m_inner.m_val + t.m_m2.m_inner.m_val >= 8) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
