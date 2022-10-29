// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );
   input clk;
   int cyc = 0;
   logic val = 0;
   // Example:
   always @(posedge clk) begin
      cyc <= cyc + 1;
      val = ~val;
      $display("t=%0t   cyc=%0d   val=%b", $time, cyc, val);
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
   assert property(@(posedge clk) cyc % 2 == 0 |=> $past(val) == 0)
      else $display("$past assert 1 failed");
   assert property(@(posedge clk) cyc % 2 == 1 |=> $past(val) == 1)
      else $display("$past assert 2 failed");
   // Example end
endmodule
