// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Member;
   rand int m_val;
endclass

class Cls;
   rand int m_val;
   rand Member m_member;

   function void test;
      automatic int rand_result;
      logic ok1 = 0, ok2 = 0;

      m_val = 256;
      m_member.m_val = 65535;
      for (int i = 0; i < 20; i++) begin
         rand_result = randomize();
         if (rand_result != 1) $stop;
         if (m_val != 256) ok1 = 1;
         if (m_member.m_val != 65535) ok2 = 1;
      end
      if (!ok1) $stop;
      if (!ok2) $stop;
   endfunction

   function new;
      m_member = new;
   endfunction
endclass

module t(/*AUTOARG*/);

   initial begin
      Cls c;
      c = new;

      c.test;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
