// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test error for packed tagged union with dynamic member types

module t;
   typedef union tagged packed {
      void Invalid;
      string Str;
   } BadUnion;

   BadUnion u;

   initial begin
      $display("Should not reach here");
      $finish;
   end
endmodule
