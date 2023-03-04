// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   parameter MTM = (1:2:3);

   initial begin
      if (MTM != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
