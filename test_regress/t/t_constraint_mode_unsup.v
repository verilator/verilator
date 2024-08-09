// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   int m_one;
   static constraint cons { m_one > 0 && m_one < 2; }
endclass

module t;
   Packet p;

   initial begin
      p = new;
      $display("p.cons.constraint_mode()=%0d", p.cons.constraint_mode());
      p.cons.constraint_mode(0);
      p.constraint_mode(0);
   end
endmodule
