// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jie Xu
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   logic [1:0][31:0] tt;
   logic [31:0]      a;
   logic [31:0]      b;
   logic [31:0]      c;

   initial begin
      a = 1;
      b = 2;
      c = 3;
      tt[0] = a;
      tt[1] = b;
      tt[2] = c;  // Out of bounds
      if (tt[0]!=a) $stop;
      if (tt[1]!=b) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
