// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   wire d, en, nc, pc;

   // verilator lint_off IMPLICIT
   cmos      (cm0, d, nc, pc);
   rcmos     (rc0, d, nc, pc);

   nmos      (nm0, d, en);
   pmos      (pm0, d, en);
   rnmos     (rn0, d, en);
   rpmos     (rp0, d, en);

   rtran     (rt0, d);
   tran      (tr0, d);

   rtranif0  (r00, d, en);
   rtranif1  (r10, d, en);
   tranif0   (t00, d, en);
   tranif1   (t10, d, en);
   // verilator lint_on IMPLICIT

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
