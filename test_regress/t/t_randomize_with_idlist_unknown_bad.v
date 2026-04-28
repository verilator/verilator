// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int m_x;
endclass

function int F(Cls obj);
  // 'm_z' is not a member of Cls -- typo.
  return obj.randomize() with (m_x, m_z) { m_x > 0; };
endfunction

module t;
  Cls c;
  initial begin
    c = new;
    if (F(c) != 1) $stop;
    $finish;
  end
endmodule
