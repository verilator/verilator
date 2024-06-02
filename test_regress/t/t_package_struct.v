// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef struct {
      string a, b;
      struct {
         bit a, b;
      } has;
   } strings;
endpackage

module t (/*AUTOARG*/);
  initial begin
     pkg::strings stct;
     stct.a = "hello";
     stct.b = "world";
     $display("%s, %s (%1b, %1b)", stct.a, stct.b, stct.has.a, stct.has.b);
     $write("*-* All Finished *-*\n");
     $finish;
  end
endmodule
