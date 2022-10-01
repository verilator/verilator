// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   mailbox #(int) m;

   initial begin
      m = new(4);
      if (m.bad_method() != 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
