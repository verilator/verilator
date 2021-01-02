// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   bit [2:0] uns;

   initial begin
      uns = 1;
      if (uns > 3'b111) $stop;
   end
endmodule
