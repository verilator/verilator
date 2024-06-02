// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;

   wire a = cyc[0];
   wire b = cyc[0];

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      // Before this was optimized, with --coverage-line
      // error: self-comparison always evaluates to true [-Werror=tautological-compare]
      //        if (((1U & vlSelf->t__DOT__cyc) == (1U & vlSelf->t__DOT__cyc)))
      if (a != cyc[0]) $stop;  // Becomes cyc == cyc after substitution
      if (b != cyc[0]) $stop;
      if (cyc==10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
