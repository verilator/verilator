// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   sub #(10,11,12,13) sub ();

endmodule

module  sub ();
   parameter A = 0;
   parameter B = 1;

   ip ip();

   parameter C = 2;
   parameter D = 3;

   initial begin
      if (A!=10) $stop;
      if (B!=11) $stop;
      if (C!=12) $stop;
      if (D!=13) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module ip;
endmodule
