// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   virtual foo vif;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
