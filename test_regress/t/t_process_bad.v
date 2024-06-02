// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   process p;

   initial begin
      if (p != null) $stop;
      p = process::self();
      if (p.bad_method() != 0) $stop;

      p.bad_method_2();

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
