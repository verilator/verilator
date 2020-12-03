// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int cyc = 0;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $strobe("[%0t] cyc=%0d", $time, cyc);
         $strobe("[%0t] cyc=%0d also", $time, cyc);
      end
      else if (cyc == 17) begin
         $strobeb(cyc, "b");
      end
      else if (cyc == 18) begin
         $strobeh(cyc, "h");
      end
      else if (cyc == 19) begin
         $strobeo(cyc, "o");
      end
      else if (cyc == 22) begin
         $strobe("[%0t] cyc=%0d new-strobe", $time, cyc);
      end
      else if (cyc == 24) begin
         $monitoroff;
      end
      else if (cyc == 26) begin
         $monitoron;
      end
      else if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
