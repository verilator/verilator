// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

// Test: Covergroup with INTERNAL clock using explicit sampling
// This demonstrates the workaround for internally generated clocks.
//
// Note: Auto-sampling with clocking events (@(posedge clk)) does NOT work
// for internal clocks due to Verilator timing scheduler limitations.
// The sample() call is generated but the NBA region isn't triggered.
//
// Solution: Call .sample() explicitly in an always block.

module t;
   logic clk = 0;
   always #5 clk = ~clk;

   logic [1:0] data;

   /* verilator lint_off UNSIGNED */
   covergroup cg;  // NOTE: No clocking event - we'll sample explicitly
      cp: coverpoint data {
         bins val0 = {2'b00};
         bins val1 = {2'b01};
         bins val2 = {2'b10};
         bins val3 = {2'b11};
      }
   endgroup
   /* verilator lint_on UNSIGNED */

   cg cg_inst = new;

   // Explicit sampling workaround for internal clocks
   always @(posedge clk) begin
      cg_inst.sample();
   end

   initial begin
      // Cycle 0
      data = 2'b00;
      @(posedge clk);

      // Cycle 1
      data = 2'b01;
      @(posedge clk);

      // Cycle 2
      data = 2'b10;
      @(posedge clk);

      // Cycle 3
      data = 2'b11;
      @(posedge clk);

      // Check coverage
      #1; // Small delay to ensure last sample completes

      begin
         automatic real cov = cg_inst.get_inst_coverage();
         $display("Coverage: %0.1f%%", cov);

         // Should have hit all 4 bins = 100%
         if (cov >= 99.0) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $display("ERROR: Expected 100%% coverage, got %f%%", cov);
            $display("ERROR: This is a known limitation - auto-sampling doesn't work with internal clocks");
            $stop;
         end
      end
   end

endmodule
