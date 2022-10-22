// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   logic [31:0] o;

   initial begin
      o = {0 {1'b1}};  // Bad 0 rep
      o = {$test$plusargs("NON-CONSTANT") {1'b1}};  // Bad non-constant rep
      $stop;
   end
endmodule
