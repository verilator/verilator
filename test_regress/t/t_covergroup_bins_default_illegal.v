// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test default bins and illegal_bins

module t;

   logic [3:0] data;
   int error_count = 0;

   // Test 1: default bins
   covergroup cg_default;
      coverpoint data {
         bins special = {0, 5, 10};
         bins others = default;  // Catch-all for uncovered values
      }
   endgroup

   // Test 2: illegal_bins (we'll test it doesn't crash on valid values)
   covergroup cg_valid;
      coverpoint data {
         bins valid = {[0:10]};
         illegal_bins reserved = {[11:15]};
      }
   endgroup

   initial begin
      cg_default cg1;
      cg_valid cg2;
      real cov;

      cg1 = new;
      cg2 = new;

      // Test 1: default bins
      $display("Test 1: default bins");
      data = 0;  cg1.sample();  // special bin
      data = 1;  cg1.sample();  // default/others bin
      data = 5;  cg1.sample();  // special bin
      data = 7;  cg1.sample();  // default/others bin
      data = 10; cg1.sample();  // special bin

      cov = cg1.get_inst_coverage();
      $display("  Coverage with default bins: %0.1f%%", cov);
      // Both bins hit: special (3 values: 0,5,10) and default (2 values: 1,7)
      // Expected: 2/2 = 100%
      if (cov < 99.0 || cov > 101.0) begin
         $display("%%Error: Expected 100%%, got %0.1f%%", cov);
         error_count++;
      end

      // Test 2: illegal_bins (test with valid values only)
      $display("Test 2: illegal_bins (sampling valid values)");
      data = 0;  cg2.sample();  // valid
      data = 5;  cg2.sample();  // valid
      data = 10; cg2.sample();  // valid

      cov = cg2.get_inst_coverage();
      $display("  Coverage with illegal_bins: %0.1f%%", cov);
      // Only the valid bin counts, illegal bins don't count toward coverage
      // 1 bin out of 1 = 100%
      if (cov < 99.0 || cov > 101.0) begin
         $display("%%Error: Expected 100%%, got %0.1f%%", cov);
         error_count++;
      end

      if (error_count == 0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $display("%%Error: %0d test(s) failed", error_count);
         $stop;
      end

      $finish;
   end

endmodule
