// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   initial begin;
      @(clk);
      $write("[%0t] Got\n", $time);
      @(clk);
      $write("[%0t] Got\n", $time);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
