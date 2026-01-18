// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when non-void tagged union member has no expression

module t;
   typedef union tagged {
      void Invalid;
      int Valid;
   } maybe_int_t;

   maybe_int_t x;

   initial begin
      // Error: Valid is non-void and requires an expression
      x = tagged Valid;
   end
endmodule
