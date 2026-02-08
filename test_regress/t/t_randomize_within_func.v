// DESCRIPTION: Verilator: Test for unsupported multiple global constraints
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int m_1;
  int m_2;
  function void test_this_randomize;
    int a;
    a = randomize(m_2) with {m_2 > 2 && m_2 < 5;};
    $display("%d: a=%0d %0d", `__LINE__, a, m_2);
    if (a != 1) $stop;
    // Problem 2 (Fixed): m_2 should be 3 or 4, but get out-of-range return
    if (!(m_2 > 2 && m_2 < 5)) $stop;
    // Problem 1 (Fixed): Got %Warning: /svaha/wsnyder/SandBox/homecvs/v4/verilator/include/verilated_random.cpp:417: Internal: Solver error: (error "line 9 column 27: invalid empty $
    a = this.randomize() with {m_1 > 5 && m_1 < 10;};
    $display("%d: a=%0d %0d", `__LINE__, a, m_1);
    if (a != 1) $stop;
    if (!(m_1 > 5 && m_1 < 10)) $stop;
  endfunction
endclass

module t_randomize_within_func;
  initial begin
    automatic Cls c = new;
    c.test_this_randomize();

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
