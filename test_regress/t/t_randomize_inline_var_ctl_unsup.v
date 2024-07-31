// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int one;
   int two;
   static int three;

   function void test;
      void'(randomize(one));
      void'(randomize(two, three));
   endfunction
endclass
