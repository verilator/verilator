// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

class Cls;
   typedef enum {A = 10, B = 20, C = 30} en_t;
endclass

   initial begin
      Cls c;
      if (c.A != 10) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
