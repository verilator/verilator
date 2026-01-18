// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when void tagged union member has an expression

module t;
   typedef union tagged {
      void Invalid;
      int Valid;
   } VInt;

   VInt v;

   initial begin
      // Error: void member should not have an expression
      v = tagged Invalid (42);
   end
endmodule
