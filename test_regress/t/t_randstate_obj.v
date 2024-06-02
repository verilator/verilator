// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   rand int length;
endclass

module t(/*AUTOARG*/);

   automatic int rand_result, v1, v2;
   automatic string s;

   initial begin
      Cls c;
      c = new;

      s = c.get_randstate();

      rand_result = c.randomize();
      if (rand_result != 1) $stop;
      v1 = c.length;

      c.set_randstate(s);

      rand_result = c.randomize();
      if (rand_result != 1) $stop;
      v2 = c.length;

`ifdef VERILATOR  // About half of the other simulators fail at this
      if (v1 != v2) $stop;
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
