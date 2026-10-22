// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  class Base;
  endclass
  class Derived extends Base;
  endclass
  class Other;
  endclass

  int m[Base];
  int n[int];
  Derived d;
  Other o;

  initial begin
    // Legal
    m[d] = 1;
    m[null] = 2;
    if (m.exists(d)) m.delete(d);
    // Illegal, index not assignment compatible
    m[o] = 3;
    if (m.exists(o)) $stop;
    m.delete(o);
    void'(m.first(o));
    n[o] = 4;
  end
endmodule
