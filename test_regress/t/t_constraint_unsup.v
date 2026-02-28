// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand real x;
  constraint cons { x + 1.0 > 0.0; }
endclass

module t;
  Packet p;

  initial begin
    p = new;
    void'(p.randomize());
  end
endmodule
