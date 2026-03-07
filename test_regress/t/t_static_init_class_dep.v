// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  class A;
    static int a = B::b + 1;
  endclass

  class B;
    static int b = 2;
  endclass

  initial begin
    if (B::b != 2) $stop;
    if (A::a != 3) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
