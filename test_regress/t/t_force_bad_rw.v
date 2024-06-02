// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   int ass[int];

   initial begin
      ass[2] = 20;

      foreach (ass[index]) begin
         force index = 0;
         $display("ii %d\n", index);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
