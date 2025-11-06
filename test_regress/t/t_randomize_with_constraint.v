// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int m_x;
  int m_y = -1;
endclass

function int func1(Cls obj, int y);
  return obj.randomize() with (
  m_x) {
    m_x > 0;
    m_x < y;
  };
endfunction

function int func2(Cls obj, int y);
  return obj.randomize() with (
  m_x) {
    m_x > 0;
    m_x < m_y;
  };
endfunction

module t;
  initial begin
    Cls c;
    int i;
    c = new;
    i = func1(c, 2);
    i = func2(c, 2);
  end
endmodule
