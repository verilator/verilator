// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   int m_one;
   constraint cons { m_one > 0 && m_one < 2; }

   function int get_constraint_mode;
      return constraint_mode();
   endfunction
endclass

module t;
   Packet p;

   initial begin
      p = new;
      p.m_one.constraint_mode(0);
      $display("p.constraint_mode()=%0d", p.constraint_mode());
      $display(p.constraint_mode(0));
      p.cons.constraint_mode();
   end
endmodule
