// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// No init value is legal with classes, as long as not used without the parameter
class Cls #(int A, int B);
endclass

module t(/*AUTOARG*/);
   initial begin
      Cls #(1) c;  // Bad: missing B
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
