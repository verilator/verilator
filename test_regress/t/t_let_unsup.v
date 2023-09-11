// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   let F(untyped a) = 30 + a;
   let G(int a) = 30 + a;
   let H(signed a) = 30 + a;

   initial begin
      if (F(1) != (30 + 1)) $stop;
      if (G(1) != (30 + 1)) $stop;
      if (H(1) != (30 + 1)) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
