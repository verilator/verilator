// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   union soft {
      bit [7:0] val1;
      bit [3:0] val2;
   } u;

   initial begin
      u.val1 = 8'h7c;
      if (u.val1 != 8'h7c) $stop;
      u.val2 = 4'h6;
      if (u.val2 != 4'h6) $stop;
      $display("%p", u);
      if (u.ual1 != 8'h76) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
