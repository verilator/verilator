// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  m1 u_1();
  m2 u_2();
  m3 u_3();
  x4 u_4();
  m5 u_5();
  other u_o();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
