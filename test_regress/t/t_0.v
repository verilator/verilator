// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   enum int unsigned {
      FIVE_INT = 5
   } FI;

   int array5i[FIVE_INT];

   initial begin
      if ($size(array5i) != 5) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
