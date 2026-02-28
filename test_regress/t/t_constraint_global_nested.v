// DESCRIPTION: Verilator: Test for unsupported multiple global constraints
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0


class Inner;
  rand int m_val;
  constraint c_inner { m_val inside {[1:10]}; }
  function new(); m_val = 0; endfunction
endclass

class Mid;
  rand Inner m_inner;
  rand int m_x;
  // Mid has global constraint on m_inner.m_val
  constraint c_mid_global {
    m_x > m_inner.m_val;
    m_x inside {[5:15]};
  }
  function new();
    m_inner = new();
    m_x = 0;
  endfunction
endclass

class Top;
  rand Mid m_mid;
  rand int m_y;
  // Top also has global constraint on m_mid.m_inner.m_val
  constraint c_top_global {
    m_y < m_mid.m_inner.m_val;
    m_y inside {[1:5]};
  }
  function new();
    m_mid = new();
    m_y = 0;
  endfunction
endclass

module t;
  Top top;
  /* verilator lint_off WIDTHTRUNC */
  initial begin
    top = new();
    if (!top.randomize()) $stop;
    $display("After randomization:");
    $display("  top.m_y = %0d", top.m_y);
    $display("  top.m_mid.m_x = %0d", top.m_mid.m_x);
    $display("  top.m_mid.m_inner.m_val = %0d", top.m_mid.m_inner.m_val);
    $write("*-* All Finished *-*\n");
    $finish;
  end
  /* verilator lint_off WIDTHTRUNC */
endmodule
