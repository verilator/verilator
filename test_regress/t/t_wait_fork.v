// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   logic never;

   integer n = 0;

   initial begin
      disable fork;
      fork
         #10 if (n != 0) $stop; else n = 1;
         #15 if (n != 1) $stop; else n = 2;
      join_none
      wait fork;
      if (n != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
