// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int t;
endclass

module Sub;
   Cls c;
   initial begin
      int i;
      c = new;
      i = c.t;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module t;
   Sub foo;
endmodule
