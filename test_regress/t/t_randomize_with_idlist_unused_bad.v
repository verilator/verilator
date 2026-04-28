// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int m_x;
  rand int m_y;
endclass

function int F(Cls obj);
  // 'm_y' is in the identifier_list but never referenced in the constraint.
  return obj.randomize() with (m_x, m_y) { m_x > 0; };
endfunction

module t;
  Cls c;
  initial begin
    c = new;
    if (F(c) != 1) $stop;
    $finish;
  end
endmodule
