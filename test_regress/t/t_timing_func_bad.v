// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   function int f;
      #1 $stop;
      f = 0;
   endfunction

   int i;

   initial begin
      i = f();
      $write("*-* All Finished *-*\n");
      $finish;
   end

   final begin
      #1;
      $stop;
   end

endmodule
