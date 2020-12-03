// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   real x;
   real y;
   var type(x+y) z;

   initial begin
      x = 1.2;
      y = 2.3;
      z = x + y;
      if (z != (1.2+2.3)) $stop;
      z = type(z)'(22);
      if (z != 22.0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
