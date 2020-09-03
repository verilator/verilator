// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   int i;
   int a;
   int b;
   initial begin
      i = $cast(a, b);
      if (i != 1) $stop;
      $cast(a, b);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
