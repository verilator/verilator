// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   initial begin
      fork : foo
         disable foo;
         #1 $stop;
      join_none
      #2;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
