// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   logic never;

   initial begin
      fork
         #10;
         #10;
      join_none
      disable fork;
      wait fork;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
