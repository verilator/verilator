// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand int x;
  rand int y;

  constraint c_power { x ** y < 10000; }
endclass

module t;

  Packet p;

  initial begin
    p = new;
    void'(p.randomize());
    $finish;
  end
endmodule
