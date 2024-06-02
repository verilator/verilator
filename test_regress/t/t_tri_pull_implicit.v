// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   // verilator lint_off IMPLICIT
   pulldown (pd);
   pullup (pu);

   initial begin
      if (pd != 0) $stop;
      if (pu != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
