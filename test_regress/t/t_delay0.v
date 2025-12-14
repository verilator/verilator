// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test ##0 delay support (zero cycle delay = immediate execution)

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int counter;
   int value;

   // Test ##0 - should execute immediately without waiting
   default clocking cb @(posedge clk);
   endclocking

   initial begin
      counter = 0;
      value = 0;

      // ##0 means no delay - execute immediately
      ##0 value = 1;
      if (value != 1) begin
         $display("ERROR: ##0 delay didn't execute immediately, value=%0d", value);
         $stop;
      end

      // ##0 followed by ##1
      ##0 value = 2;
      ##1 value = 3;

      // At this point, value should be 3 (after 1 clock)
      if (value != 3) begin
         $display("ERROR: After ##0 and ##1, value=%0d (expected 3)", value);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @(posedge clk) begin
      counter <= counter + 1;
      if (counter > 100) begin
         $display("ERROR: Timeout");
         $stop;
      end
   end
endmodule
