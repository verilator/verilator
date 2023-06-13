// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   rand int m_val;

   function void test;
      automatic int rand_result;

      rand_result = randomize();
      if (rand_result != 1) $stop;
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
