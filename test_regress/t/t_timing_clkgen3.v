// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`timescale 10ns / 1ns

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

module t;
   logic clk  = 0;
   logic clk_copy;
   int   cyc  = 0;
   int   cnt1 = 0;
   int   cnt2 = 0;

   initial forever #1 clk = ~clk;

   always @(negedge clk) begin
       #0.75 cnt1++;
       `WRITE_VERBOSE(("[%0t] NEG clk (%b)\n", $time, clk));
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      #0.5 `WRITE_VERBOSE(("[%0t] POS clk (%b)\n", $time, clk));
      if (cyc == 5) begin
         if (cnt1 != 4 && cnt2 != 9) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   assign clk_copy = clk;
   always @(posedge clk_copy or negedge clk_copy) begin
       #0.25 cnt2++;
       `WRITE_VERBOSE(("[%0t] POS/NEG clk_copy (%b)\n", $time, clk_copy));
   end

   initial #100 $stop; // timeout
endmodule
