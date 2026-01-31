// DESCRIPTION: Verilator: Test for case-matches with non-pattern condition
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   typedef union tagged {
      int Valid;
      void Invalid;
   } maybe_int;

   initial begin
      maybe_int v;
      v = tagged Valid (42);

      // This should be an error - case-matches requires tagged patterns
      case (v) matches
        42: $display("wrong");  // Error: not a tagged pattern
        default: $display("ok");
      endcase

      $write("*-* All Coverage Coverage *-*\n");
      $finish;
   end
endmodule
