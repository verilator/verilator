// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk,
   d
   );

   input clk;
   input d;
   wire delayed_CLK;
   wire delayed_D;
   reg notifier;
   wire [1:0] BL_X = 2'b11;
   wire [5:0] BL_X2;
   wire BL_0;
   wire [3:0] BL_1 = 4'b1100;

   logic[3:0] sh1 = 1;
   logic[3:0] sh2 = 2;
   logic[3:0] sh3 = 3;
   logic[3:0] sh4 = 4;

   int cyc = 0;

   specify
      $setuphold (posedge clk, negedge d, 0, 0, notifier,,, delayed_CLK, delayed_D);
      $setuphold (posedge sh1, negedge sh3, 0, 0, notifier,,, sh2, sh4);
      $setuphold (posedge clk, negedge d, 0, 0);
      $setuphold (posedge clk, negedge d, (0:0:0), (0:0:0));
      $setuphold (posedge clk, negedge d, 0, 0,,,,,);
      $setuphold (posedge clk &&& sh1, BL_X[0], 0, 0, ,,,delayed_CLK, BL_0);
      $setuphold (posedge clk &&& sh1, BL_1, 0, 0, ,,,delayed_CLK, BL_X2[4:1]);
   endspecify

   initial begin
      if (sh1 != sh2 || sh3 != sh4) begin
         $stop;
      end
      if (BL_0 != BL_X[0] || BL_1 != BL_X2[4:1]) begin
         $stop;
      end
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      $display("%d %d", clk, delayed_CLK);
      if (delayed_CLK != clk || delayed_D != d) begin
         $stop;
      end
      if (cyc == 10) begin
         $display("*-* All Finished *-*");
         $finish;
      end
   end
endmodule
