// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer cyc; initial cyc=1;

   // verilator lint_off LATCH
   // verilator lint_off UNOPT
   // verilator lint_off UNOPTFLAT
   // verilator lint_off MULTIDRIVEN
   // verilator lint_off BLKANDNBLK

   reg [31:0] comcnt;
   reg [31:0] dlycnt;  initial dlycnt=0;
   reg [31:0] lastdlycnt; initial lastdlycnt = 0;

   reg [31:0] comrun;  initial comrun = 0;
   reg [31:0] comrunm1;
   reg [31:0] dlyrun;  initial dlyrun = 0;
   reg [31:0] dlyrunm1;
   always @ (posedge clk) begin
      $write("[%0t] cyc %d\n", $time,cyc);
      cyc <= cyc + 1;
      if (cyc==2) begin
         // Test # of iters
         lastdlycnt = 0;
         comcnt = 0;
         dlycnt <= 0;
      end
      if (cyc==3) begin
         dlyrun <= 5;
         dlycnt <= 0;
      end
      if (cyc==4) begin
         comrun = 4;
      end
   end
   always @ (negedge clk) begin
      if (cyc==5) begin
         $display("%d %d\n", dlycnt, comcnt);
         if (dlycnt != 32'd5) $stop;
         if (comcnt != 32'd19) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // This forms a "loop" where we keep going through the always till comrun=0
   reg runclk;  initial runclk = 1'b0;
   always @ (/*AS*/comrunm1 or dlycnt) begin
      if (lastdlycnt != dlycnt) begin
         comrun = 3;
         $write ("[%0t] comrun=%0d start\n", $time, comrun);
      end
      else if (comrun > 0) begin
         comrun = comrunm1;
         if (comrunm1==1) begin
            runclk = 1;
            $write ("[%0t] comrun=%0d [trigger clk]\n", $time, comrun);
         end
         else $write ("[%0t] comrun=%0d\n", $time, comrun);
      end
      lastdlycnt = dlycnt;
   end

   always @ (/*AS*/comrun) begin
      if (comrun!=0) begin
         comrunm1 = comrun - 32'd1;
         comcnt = comcnt + 32'd1;
         $write("[%0t]                comcnt=%0d\n", $time,comcnt);
      end
   end

   // This forms a "loop" where we keep going through the always till dlyrun=0
   reg runclkrst;
   always @ (posedge runclk) begin
      runclkrst <= 1;
      $write ("[%0t] runclk\n", $time);
      if (dlyrun > 0) begin
         dlyrun <= dlyrun - 32'd1;
         dlycnt <= dlycnt + 32'd1;
         $write ("[%0t]   dlyrun<=%0d\n", $time, dlyrun-32'd1);
      end
   end

   always @* begin
      if (runclkrst) begin
         $write ("[%0t] runclk reset\n", $time);
         runclkrst = 0;
         runclk = 0;
      end
   end

endmodule
