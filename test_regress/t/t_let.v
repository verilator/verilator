// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
   let P = 11;
   let PP(a) = 30 + a;
endpackage

module t(/*AUTOARG*/);

   let A = 10;
   let B() = 20;
   let C(a) = 30 + a;
   let D(a, b) = 30 + a + b;
   let E(a=1, b=7) = 30 + a + b;
   let F(untyped a) = 30 + a;

   initial begin
      if (A != 10) $stop;
      if (A() != 10) $stop;
      if (B != 20) $stop;
      if (B() != 20) $stop;
      if (C(1) != (30 + 1)) $stop;
      if (C(.a(1)) != (30 + 1)) $stop;
      if (D(1, 2) != (30 + 1 + 2)) $stop;
      if (D(.a(1), .b(2)) != (30 + 1 + 2)) $stop;
      if (E(2) != (30 + 2 + 7)) $stop;
      if (E(.b(1)) != (30 + 1 + 1)) $stop;
      if (F(1) != (30 + 1)) $stop;
      if (Pkg::P != 11) $stop;
      if (Pkg::PP(6) != (30 + 6)) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
