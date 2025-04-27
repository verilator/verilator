// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk,
   d,
   t_in
   );

   input clk;
   input d;
   input t_in;
   wire delayed_CLK;
   wire delayed_D;
   reg notifier;
   wire [1:0] BL_X = 2'b11;
   wire [5:0] BL_X2;
   wire BL_0;
   wire [3:0] BL_1 = 4'b1100;
   wire fake_CLK;
   wire fake_D;

   logic[3:0] sh1 = 1;
   logic[3:0] sh2 = 2;
   logic[3:0] sh3 = 3;
   logic[3:0] sh4 = 4;
   logic[3:0] sh5 = 5;
   logic[3:0] sh6 = 6;

   int cyc = 0;

   specify
      $setuphold (posedge clk, negedge d, 0, 0, notifier, (0:0:0), 0, delayed_CLK, delayed_D);
      $setuphold (posedge sh1, negedge sh3, 0, 0, notifier,,, sh2, sh4);
      $setuphold (posedge sh5, negedge d, 0, 0, notifier,,, sh6);
      $setuphold (posedge clk, negedge d, 0, 0, notifier, (1:2:3), (0:0:0));
      $setuphold (posedge clk, negedge d, 0, 0, notifier, (1:2:3));
      $setuphold (posedge clk, negedge d, 0, 0, notifier);
      $setuphold (posedge clk, negedge d, 0, 0);
      $setuphold (posedge clk, negedge d, 0, 0);
      $setuphold (posedge clk, negedge d, (0:0:0), (0:0:0));
      $setuphold (posedge clk, negedge d, 0:0:0, 0:0:0);
      $setuphold (posedge clk, negedge d, 0, 0,,,,,);

      $setuphold (posedge clk &&& sh1, BL_X[0], 0, 0, ,,,delayed_CLK, BL_0);
      $setuphold (posedge clk &&& sh1, BL_1, 0, 0, ,,,delayed_CLK, BL_X2[4:1]);

      $setuphold (fake_CLK, fake_D &&& sh1, 0, 0);
      $setuphold (posedge fake_CLK, posedge fake_D &&& sh1, 0, 0);
      $setuphold (negedge fake_CLK, negedge fake_D &&& sh1, 0, 0);
      $setuphold (edge fake_CLK, edge fake_D &&& sh1, 0, 0);
      $setuphold (edge [0Z, z1, 10] fake_CLK, edge [01, x0, 0X] fake_CLK &&& sh1, 0, 0);

      $setuphold (posedge clk, negedge d, 0, 0, notifier, (0:0:0), 0, t_in);
   endspecify

   initial begin
      if (sh1 != sh2 || sh3 != sh4) begin
         $stop;
      end
      if (sh5 != sh6) begin
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
