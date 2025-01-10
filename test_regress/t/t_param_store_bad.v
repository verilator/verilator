// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t #(
           string S = "<unset>"
           );

   initial begin
      $value$plusargs("S=%s", S);  // BAD assignment to S
      #1;  // Original bug got compile time error only with this line
      $display("S=%s", S);
      $finish;
   end

endmodule
