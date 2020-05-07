// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Should have been:
//module t #(

module t
  (
   FOO=1
   ) (
      output bar
      );

   assign bar = FOO;

endmodule
