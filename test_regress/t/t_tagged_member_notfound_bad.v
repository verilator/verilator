// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when tagged expression uses non-existent member

/* verilator lint_off WIDTHEXPAND */

module t;
   typedef union tagged {
      void Invalid;
      int Valid;
   } VInt;

   VInt v;

   initial begin
      // Error: member 'NonExistent' not found in union
      v = tagged NonExistent 42;
   end
endmodule
