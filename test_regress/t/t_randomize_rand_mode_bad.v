// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   int m_val;
   rand int m_other_val;
   rand logic [7:0] m_pack;

   function int get_rand_mode;
      return rand_mode();
   endfunction
endclass

module t;
   Packet p;

   initial begin
      p = new;
      p.m_val.rand_mode(0);
      p.m_pack[0].rand_mode(0);
      $display("p.rand_mode()=%0d", p.rand_mode());
      $display(p.rand_mode(0));
      p.m_other_val.rand_mode();
   end
endmodule
