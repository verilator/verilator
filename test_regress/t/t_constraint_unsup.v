// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand real x;
  constraint cons { x + 1.0 > 0.0; }
endclass

class Wildcard;
  rand int w[*];
  constraint c { w[3] == 5; }
endclass

module t;
  Packet p;
  Wildcard w;
  initial begin
    p = new;
    w = new;
    void'(p.randomize());
    void'(w.randomize());
  end
endmodule
