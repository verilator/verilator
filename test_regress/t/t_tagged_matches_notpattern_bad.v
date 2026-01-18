// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error when matches is used without a tagged pattern

module t;
   typedef union tagged {
      void Invalid;
      int Valid;
   } maybe_int_t;

   maybe_int_t x;

   initial begin
      // Error: pattern should be "tagged Valid .v" not just "1"
      if (x matches 1)
        $display("matched");
   end
endmodule
