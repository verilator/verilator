// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   union {
      bit [7:0] val1;
      bit [3:0] val2;
      real      r;
   } u;

   initial begin
      u.val1 = 8'h7c;
      if (u.val1 != 8'h7c) $stop;
      if (u.val2 != 4'hc) $stop;
      u.r = 1.24;
      if (u.r != 1.24) $stop;
      $display("%p", u);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
