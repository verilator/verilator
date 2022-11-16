// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 100ns/1ns

module t;
   int   ia;
   int   ib;

   initial begin
      ia = 0;
      #1 ib = ++ia;
      #1
        if (ia !== ib) $stop;

      #1 ib = ia++;
      #1
        if (ia == ib) $stop;
      #10;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
