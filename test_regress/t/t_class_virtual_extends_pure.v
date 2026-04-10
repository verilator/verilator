// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolay Puzanov
// SPDX-License-Identifier: CC0-1.0

virtual class Base;
  pure virtual function void f0();
endclass

virtual class Child extends Base;
  pure virtual function void f1();
endclass

class Impl extends Child;
  virtual function void f0();
  endfunction
  virtual function void f1();
  endfunction
endclass

module t;
endmodule
