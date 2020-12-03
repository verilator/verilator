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
         $monitor("[%0t] cyc=%0d", $time, cyc);
      end
      else if (cyc == 17) begin
         $monitorb(cyc, "b");
      end
      else if (cyc == 18) begin
         $monitorh(cyc, "h");
      end
      else if (cyc == 19) begin
         $monitoro(cyc, "o");
      end
      else if (cyc == 22) begin
         $monitor("[%0t] cyc=%0d new-monitor", $time, cyc);
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
