// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   function void test;
      automatic string s;

      s = get_randstate();
      // Vlt only result check
      if (s[0] !== "R") $fatal(2, $sformatf("Bad get_randstate = '%s'", s));

      set_randstate("000bad");  // Bad
      set_randstate("Zdlffjfmkmhodjcnddlffjfmkmhodjcnd");  // Bad
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
