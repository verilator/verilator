// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
   let P = 11;
endpackage

module t(/*AUTOARG*/);

   let A = 10;
   let B() = 20;
   let C(a) = 30 + a;
   let D(a, b) = 30 + a + b;
   let E(a, b=7) = 30 + a + b;
   let F(untyped a) = 30 + a;
   let G(int a) = 30 + a;

   initial begin
      if (A != 10) $stop;
      if (A() != 10) $stop;
      if (B != 20) $stop;
      if (B() != 20) $stop;
      if (C(1) != (30 + 1)) $stop;
      if (D(1, 2) != (30 + 1 + 2)) $stop;
      if (E(1) != (30 + 1 + 7)) $stop;
      if (F(1) != (30 + 1)) $stop;
      if (G(1) != (30 + 1)) $stop;
      if (Pkg::P != 11) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
