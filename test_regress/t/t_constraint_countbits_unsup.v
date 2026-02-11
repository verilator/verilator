// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Test: non-constant control in $countbits inside constraint (unsupported)

class Packet;
  rand bit [7:0] value;
  bit ctrl;
  constraint cons { $countbits(value, ctrl) == 3; }
endclass

module t;
  Packet p;

  initial begin
    p = new;
    void'(p.randomize());
  end
endmodule
