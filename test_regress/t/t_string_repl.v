// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   string s, s2;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      s = {s2, {cyc{"*"}}};
      if (cyc != s.len()) $stop;
      if (cyc == 0 && s != "") $stop;
      if (cyc == 1 && s != "*") $stop;
      if (cyc == 2 && s != "**") $stop;
      if (cyc == 3 && s != "***") $stop;
      if (cyc == 4 && s != "****") $stop;
      if (cyc == 5 && s != "*****") $stop;
      if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
