// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

module t;
   logic clk = 0;
   logic clk_inv;
   int   cnt1 = 0;
   int   cnt2 = 0;

   always #4 clk = ~clk;
   always @(posedge clk) begin
       cnt1 <= cnt1 + 1;
       `WRITE_VERBOSE(("[%0t] clk (%b)\n", $time, clk));
   end

   assign #2 clk_inv = ~clk;
   initial forever begin
       @(posedge clk_inv) cnt2++;
       `WRITE_VERBOSE(("[%0t] clk_inv (%b)\n", $time, clk_inv));
   end

   initial #81 begin
       if (cnt1 != 10 && cnt2 != 10) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
   end
endmodule
