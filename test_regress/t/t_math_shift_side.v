// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int m_n_bits;

   function int get_n_bytes;
      return ((m_n_bits - 1) / 8) + 1;
   endfunction

endclass

module t(/*AUTOARG*/);

   int  i;

   initial begin
      Cls c;
      c = new;

      c.m_n_bits = 23;
      if (c.get_n_bytes() != 3) $stop;

      i = 1 << c.get_n_bytes();
      if (i != 8) $stop;

      i = 32'h1234 >> c.get_n_bytes();
      if (i != 32'h246) $stop;

      i = 32'shffffffff >>> c.get_n_bytes();
      if (i != 32'hffffffff) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
