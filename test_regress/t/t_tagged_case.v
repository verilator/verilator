// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test case pattern matching with tagged unions
// IEEE 1800-2023 Section 12.6.1

module t;

   // Basic tagged union (IEEE example)
   typedef union tagged {
      void Invalid;
      int Valid;
   } VInt;

   VInt v;
   int result;

   initial begin
      // Test 1: Basic case matches with void tag
      v = tagged Invalid;
      result = 0;
      case (v) matches
         tagged Invalid : result = 1;
         tagged Valid .n : result = n;
      endcase
      if (result !== 1) $stop;

      // Test 2: Case matches with value binding
      v = tagged Valid (123);
      result = 0;
      case (v) matches
         tagged Invalid : result = -1;
         tagged Valid .n : result = n;
      endcase
      if (result !== 123) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
