// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base #(type T = integer);
   T m_count;

   function void test1();
      if (this.m_count != 0) $stop;
      if (this.m_count++ != 0) $stop;
      if (this.m_count != 1) $stop;
      if (m_count++ != 1) $stop;
      if (this.m_count != 2) $stop;
   endfunction
endclass

class Cls #(type T = integer) extends Base #(T);
endclass

module t;
   Cls #(int) c;

   initial begin
      c = new;
      c.test1();

      c.m_count = 0;
      if (c.m_count != 0) $stop;
      if (c.m_count++ != 0) $stop;
      if (c.m_count != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
