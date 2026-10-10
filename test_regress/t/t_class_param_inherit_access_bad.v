// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class base #(int N = 1);
  local typedef bit [N-1:0] T;
endclass

class holder #(type T = int);
  T value;
endclass

class derived extends base #(7);
`ifdef TEST_PIN
  holder #(T) h;
  holder #(type(T)) queried;
  holder #(struct packed { T value; }) structured;
`else
  T value;
`endif
endclass

module t;
  derived d;
endmodule
