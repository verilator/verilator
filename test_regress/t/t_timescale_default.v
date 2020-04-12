// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Intentionally no timescale here, nor in driver file
module t;
   initial begin
      // Unspecified, but general consensus is 1s is default timeunit
      $printtimescale;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
