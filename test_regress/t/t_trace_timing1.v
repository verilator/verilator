// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(/*AUTOARG*/);

   localparam CLOCK_CYCLE = 10;

   logic rst;
   logic clk;

   initial begin
      $dumpfile({`STRINGIFY(`TEST_OBJ_DIR),"/simx.vcd"});
      $dumpvars;
   end

   always #(CLOCK_CYCLE/2) clk = ~clk;

   always begin
      rst = 1;
      clk = 0;
      $display("[%0t] rst: %d, rst: %d", $time, rst, rst);

      #CLOCK_CYCLE;
      rst = 0;
      $display("[%0t] rst: %d, rst: %d", $time, rst, rst);

      #CLOCK_CYCLE;
      $display("[%0t] rst: %d, rst: %d", $time, rst, rst);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
