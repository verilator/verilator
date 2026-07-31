// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class C;
  typedef logic [1:0] T;
  static int y = 1;
endclass : C

class P #(
    type C
);
  localparam type C1_t = C.T;
  parameter type C2_t = C.y;
  C1_t x = '1;
  C2_t y = 2;
endclass : P

module t ();
  P #(C) P_data = new();
  initial begin
    if (P_data.x != '1) $stop;
    if (P_data.y != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
