// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc=0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      $display("TestCase at %1t (%s)", $realtime, cyc[0] ? "Option1" : "Option2");
      if (cyc==9) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
