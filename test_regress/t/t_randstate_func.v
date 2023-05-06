// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   rand int length;

   function void test;
      automatic int rand_result, v1, v2;
      automatic string s;

      // UVM 2023 does a print, so check is ascii
      $display("get_randstate = '%s'", get_randstate());

      s = get_randstate();

      rand_result = randomize();
      if (rand_result != 1) $stop;
      v1 = length;

      set_randstate(s);

      rand_result = randomize();
      if (rand_result != 1) $stop;
      v2 = length;

`ifdef VERILATOR  // About half of the other simulators fail at this
      if (v1 != v2) $stop;
`endif
   endfunction
endclass

module t(/*AUTOARG*/);

   automatic int rand_result, v1, v2;
   automatic string s;

   initial begin
      Cls c;
      c = new;
      c.test;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
