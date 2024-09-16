// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(/*AUTOARG*/);

   event ev_test;

   int i;

   bit toggle = 1'b0;

   bit clk;
   always #10 clk = ~clk;

   initial begin
      @(posedge clk);

      @(ev_test);
      toggle = ~toggle;
   end

   initial begin
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars(0, top);
      for(i=0; i < 10; i++) begin
         @(posedge clk);

         if (i == 5)
           ->ev_test;
      end

      @(posedge clk);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
