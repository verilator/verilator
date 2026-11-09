// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class base #(int N = 1);
  local typedef bit [N-1:0] T;
endclass

class derived extends base #(7);
  T value;
endclass

module t;
  derived d;
endmodule
