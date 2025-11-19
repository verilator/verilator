// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Simple test for global constraints with 2-level nesting: Top -> Mid -> Inner

class Inner;
  rand int m_val;
  rand int m_rand_in_val;
  rand int m_only_topConstrained_val;
  constraint c_inner { m_val inside {[1:5]}; }

  function new();
    m_val = 0;
    m_rand_in_val = 0;
    m_only_topConstrained_val = 0;
  endfunction
endclass

class Mid;
  int m_limit;
  rand int m_x;
  rand Inner m_inner;
  rand int m_rand_mid_val;
  constraint c_mid { m_x == m_limit; }

  function new(int lim);
    m_limit = lim;
    m_x = 0;
    m_rand_mid_val = 0;
    m_inner = new();
  endfunction
endclass

class Top;
  rand Mid m_mid;
  rand int m_y;

  constraint c_top {
    m_y < m_mid.m_x;                    // 1-level reference
    m_mid.m_inner.m_val < m_y;          // 2-level reference
    m_mid.m_inner.m_only_topConstrained_val == 5;   // Only constrained at top level
  }

  function new();
    m_mid = new(10);
    m_y = 0;
  endfunction
endclass

module t_constraint_global_random_simple;
  int success;
  Top t;

  initial begin
    t = new();

    // Test: Regular randomize() with global constraints
    success = t.randomize();
    if (success != 1) $stop;

    $display("After randomization:");
    $display("  t.m_y = %0d", t.m_y);
    $display("  t.m_mid.m_x = %0d", t.m_mid.m_x);
    $display("  t.m_mid.m_inner.m_val = %0d", t.m_mid.m_inner.m_val);
    $display("  t.m_mid.m_inner.m_only_topConstrained_val = %0d", t.m_mid.m_inner.m_only_topConstrained_val);
    $display("  t.m_mid.m_rand_mid_val = %0d", t.m_mid.m_rand_mid_val);
    $display("  t.m_mid.m_inner.m_rand_in_val = %0d", t.m_mid.m_inner.m_rand_in_val);

    // Verify constraints
    // 1. c_mid: m_x == m_limit
    if (t.m_mid.m_x != 10) begin
      $display("ERROR: m_mid.m_x should be 10, got %0d", t.m_mid.m_x);
      $stop;
    end

    // 2. c_inner: m_val in [1:5]
    if (t.m_mid.m_inner.m_val < 1 || t.m_mid.m_inner.m_val > 5) begin
      $display("ERROR: m_inner.m_val should be in [1:5], got %0d", t.m_mid.m_inner.m_val);
      $stop;
    end

    // 3. c_top: m_y < m_mid.m_x (m_y < 10)
    if (t.m_y >= t.m_mid.m_x) begin
      $display("ERROR: m_y should be < m_mid.m_x, got m_y=%0d, m_x=%0d", t.m_y, t.m_mid.m_x);
      $stop;
    end

    // 4. c_top: m_mid.m_inner.m_val < m_y
    if (t.m_mid.m_inner.m_val >= t.m_y) begin
      $display("ERROR: m_inner.m_val should be < m_y, got m_val=%0d, m_y=%0d",
               t.m_mid.m_inner.m_val, t.m_y);
      $stop;
    end

    // 5. c_top: m_mid.m_inner.m_only_topConstrained_val == 5
    if (t.m_mid.m_inner.m_only_topConstrained_val != 5) begin
      $display("ERROR: m_only_topConstrained_val should be 5, got %0d",
               t.m_mid.m_inner.m_only_topConstrained_val);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
