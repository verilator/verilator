// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module s;
   parameter A = 0;
   generate
      if (A == 1)
            int i;
      else if (A == 2)
                 int i;
      else
           int i;
   endgenerate
   generate
      if (A == 1)
            int i;
      else if (A == 2)
                 int i;
      else
           int i;
   endgenerate
endmodule

module t;
   s #(0) s0();
   s #(1) s1();
   s #(2) s2();
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
