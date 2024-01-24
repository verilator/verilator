// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   in
   );
   input int in;

   int ass_keptdead;

   initial begin
      if (in != 0) begin
         ass_keptdead = 1 | in;
         $display("Avoid gate removing");
         ass_keptdead = 2 | in;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
