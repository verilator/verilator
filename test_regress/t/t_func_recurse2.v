// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   function automatic int recurse_1;
      input int i;
      if (i == 0) recurse_1 = 0;
      else recurse_1 = i + recurse_2(i);
   endfunction

   function automatic int recurse_2;
      input int i;
      return recurse_1(i - 1) * 2;
   endfunction

   initial begin
      if (recurse_1(0) != 0) $stop;
      if (recurse_1(3) != (3 + 2*(2 + 2*(1)))) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
