// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  class B;
    function void B();
    endfunction
  endclass

  class A;
    B b = B::new();

    function void B();
      b.B();
      $write("*-* All Finished *-*\n");
      $finish;
    endfunction
  endclass

  initial begin
    static A a = A::new();
    a.B();
  end
endmodule
