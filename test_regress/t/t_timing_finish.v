// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

program t;
   initial begin
      #1;
      $write("*-* All Finished *-*\n");
      // No $finish
   end
endprogram
