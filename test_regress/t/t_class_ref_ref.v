// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls#(type T = bit);
endclass

module t(/*AUTOARG*/);

   Cls#(bit) cb;

   Cls#(Cls#(bit)) ccb;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
