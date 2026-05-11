// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int m_x;
  rand int m_y;
endclass

// 'm_z' is not a member of Cls -- typo (rejected as IEEE 1800-2023 18.7 violation).
function int F_unknown(Cls obj);
  return obj.randomize() with (m_x, m_z) { m_x > 0; };
endfunction

// 'm_y' is a class member but never referenced in the constraint -- flagged unused.
function int F_unused(Cls obj);
  return obj.randomize() with (m_x, m_y) { m_x > 0; };
endfunction

module t;
  Cls c;
  initial begin
    c = new;
    if (F_unknown(c) != 1) $stop;
    if (F_unused(c) != 1) $stop;
    $finish;
  end
endmodule
