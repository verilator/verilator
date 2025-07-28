// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int m_one;
   constraint cons { $onehot(m_one) == 1; }
endclass

module t;
   Packet p;

   initial begin
      p = new;
      void'(p.randomize());
   end
endmodule
