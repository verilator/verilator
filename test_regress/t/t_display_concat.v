// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int   cyc = 0;
   always @ (posedge clk) ++cyc;

   reg [15 : 0] t2;

   always@(posedge clk) begin
      if (cyc == 0) begin
         t2 <= 16'd0;
      end
      else if (cyc == 2) begin
         t2 <= 16'habcd;
      end
      else if (cyc == 4) begin
         $display("abcd=%x", t2);
         $display("ab0d=%x", { t2[15:8], 4'd0, t2[3:0] });
         $write("*-* All Finished *-*\n");
         $finish(32'd0);
      end
   end
endmodule
