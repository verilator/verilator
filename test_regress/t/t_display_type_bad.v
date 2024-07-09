// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   string s = "a string";
   initial begin
      $display("%d %x %f %t", s, s, s, s);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
