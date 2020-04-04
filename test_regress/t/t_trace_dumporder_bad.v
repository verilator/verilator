// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   initial begin
      // Check error when this missing: $dumpfile("/should/not/be/opened");
      $dumpvars;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
