// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int m_dyn_arr[];
   rand int m_unp_arr[10];
   rand struct { int y; } m_struct;
   static rand int m_static;
endclass

module t;
   initial begin
      Packet p = new;
      p.m_dyn_arr[0].rand_mode(0);
      p.m_unp_arr[0].rand_mode(0);
      p.m_struct.y.rand_mode(0);
      p.m_static.rand_mode(0);
      $display("p.m_static.rand_mode()=%0d", p.m_static.rand_mode());
      p.rand_mode(0);
   end
endmodule
