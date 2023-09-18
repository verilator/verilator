// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   sub s1();
endmodule

module sub (/*AUTOARG*/);
   enum {s0, s1} state;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
