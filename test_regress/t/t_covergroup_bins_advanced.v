// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test advanced bin types that ARE supported:
// - ignore_bins
// - wildcard bins
// - array bins (explicit values only, not ranges yet)

module t;

   logic [3:0] data;
   int error_count = 0;

   // Test 1: ignore_bins
   covergroup cg_ignore;
      coverpoint data {
         bins low = {[0:3]};
         bins mid = {[4:7]};
         bins high = {[8:11]};
         ignore_bins reserved = {[12:15]};  // Should not count toward coverage
      }
   endgroup

   // Test 2: Array bins (with ranges - now working!)
   covergroup cg_array;
      coverpoint data {
         bins values[] = {[0:3]};  // Creates 4 bins: values[0], values[1], values[2], values[3]
      }
   endgroup

   // Test 3: wildcard bins (with don't-care bits)
   covergroup cg_wildcard;
      coverpoint data {
         wildcard bins pattern0 = {4'b00??};  // Matches 0,1,2,3
         wildcard bins pattern1 = {4'b01??};  // Matches 4,5,6,7
         wildcard bins pattern2 = {4'b10??};  // Matches 8,9,10,11
         wildcard bins pattern3 = {4'b11??};  // Matches 12,13,14,15
      }
   endgroup

   initial begin
      cg_ignore cg1;
      cg_array cg2;
      cg_wildcard cg3;
      real cov;

      cg1 = new;
      cg2 = new;
      cg3 = new;

      // Test 1: ignore_bins
      $display("Test 1: ignore_bins");
      data = 0;  cg1.sample();  // low
      data = 5;  cg1.sample();  // mid
      data = 9;  cg1.sample();  // high
      data = 12; cg1.sample();  // ignored - should not affect coverage
      data = 13; cg1.sample();  // ignored

      cov = cg1.get_inst_coverage();
      $display("  Coverage with ignore_bins: %0.1f%% (expect 100%%)", cov);
      // 3 out of 3 non-ignored bins = 100%
      if (cov < 99.0 || cov > 101.0) begin
         $display("%%Error: Expected 100%%, got %0.1f%%", cov);
         error_count++;
      end

      // Test 2: Array bins
      $display("Test 2: Array bins (with ranges)");
      data = 0; cg2.sample();  // values[0]
      data = 1; cg2.sample();  // values[1]
      data = 2; cg2.sample();  // values[2]
      // Note: values[3] not sampled, so 75% coverage expected

      cov = cg2.get_inst_coverage();
      $display("  Coverage with array bins: %0.1f%% (expect 75%%)", cov);
      // 3 out of 4 bins = 75%
      if (cov < 74.0 || cov > 76.0) begin
         $display("%%Error: Expected 75%%, got %0.1f%%", cov);
         error_count++;
      end

      // Test 3: Wildcard bins
      $display("Test 3: Wildcard bins");
      data = 2;  cg3.sample();  // pattern0 (00??)
      data = 5;  cg3.sample();  // pattern1 (01??)
      data = 10; cg3.sample();  // pattern2 (10??)
      // pattern3 not sampled, so 75% coverage

      cov = cg3.get_inst_coverage();
      $display("  Coverage with wildcard bins: %0.1f%% (expect 75%%)", cov);
      // 3 out of 4 bins = 75%
      if (cov < 74.0 || cov > 76.0) begin
         $display("%%Error: Expected 75%%, got %0.1f%%", cov);
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
