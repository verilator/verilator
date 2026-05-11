// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Output arg of class type-parameter accepts a base handle (upcast).

class Fifo #(type T = int);
  T m_val;
  task get(output T t);
    t = m_val;
  endtask
endclass

class Base;
  int m_id = 10;
endclass

class Deriv extends Base;
  int m_extra = 20;
endclass

module t;
  Fifo #(Deriv) f;
  Base b;
  Deriv d;
  initial begin
    f = new;
    d = new;
    d.m_id = 42;
    d.m_extra = 99;
    f.m_val = d;
    f.get(b);
    if (b === null) $stop;
    if (b.m_id !== 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
