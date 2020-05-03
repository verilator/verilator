// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

class Cls;
   typedef enum {A = 10, B = 20, C = 30} en_t;

   local int m_loc = 2;
   protected int m_prot = B;
endclass

   initial begin
      Cls c;
      if (c.A != 10) $stop;
      c = new;
      if (c.m_loc != 2) $stop;
      c.m_loc = 10;
      if (c.m_loc != 10) $stop;
      if (c.m_prot != 20) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
