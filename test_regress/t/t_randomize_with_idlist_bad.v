// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int m_x;
endclass

function int func(Cls obj);
  return obj.randomize() with (m_x + 1) {
    m_x > 0;
  };
endfunction

module t;
  initial begin
    Cls c;
    int i;
    c = new;
    i = func(c);
  end
endmodule
