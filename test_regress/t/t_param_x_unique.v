// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub #(parameter P = 1'bx);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module t;
   sub sub();
endmodule
