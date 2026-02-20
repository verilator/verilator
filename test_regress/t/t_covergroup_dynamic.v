// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test dynamic covergroup creation with 'new' operator

module t;

   covergroup cg;
      coverpoint data {
         bins low  = {[0:1]};
         bins high = {[2:3]};
      }
   endgroup

   int data;

   initial begin
      cg cg_inst;
      real cov;

      // Test 1: Create single dynamic instance
      $display("Test 1: Single dynamic instance");
      cg_inst = new;

      // Initially no coverage
      cov = cg_inst.get_inst_coverage();
      $display("  Initial coverage: %f", cov);
      if (cov != 0.0) $stop;

      // Sample low bin
      data = 0;
      cg_inst.sample();
      cov = cg_inst.get_inst_coverage();
      $display("  After sampling low: %f", cov);
      if (cov < 49.0 || cov > 51.0) $stop;  // ~50%

      // Sample high bin
      data = 2;
      cg_inst.sample();
      cov = cg_inst.get_inst_coverage();
      $display("  After sampling high: %f", cov);
      if (cov < 99.0 || cov > 101.0) $stop;  // ~100%

      // Test 2: Multiple dynamic instances
      $display("Test 2: Multiple dynamic instances");
      begin
         cg cg1, cg2, cg3;

         cg1 = new;
         cg2 = new;
         cg3 = new;

         // Sample different bins in each
         data = 0;
         cg1.sample();

         data = 2;
         cg2.sample();

         data = 1;
         cg3.sample();

         // Check individual coverage
         cov = cg1.get_inst_coverage();
         $display("  cg1 coverage: %f", cov);
         if (cov < 49.0 || cov > 51.0) $stop;  // 50%

         cov = cg2.get_inst_coverage();
         $display("  cg2 coverage: %f", cov);
         if (cov < 49.0 || cov > 51.0) $stop;  // 50%

         cov = cg3.get_inst_coverage();
         $display("  cg3 coverage: %f", cov);
         if (cov < 49.0 || cov > 51.0) $stop;  // 50%
      end

      // Test 3: Reassignment (old instance should be cleaned up)
      $display("Test 3: Instance reassignment");
      cg_inst = new;  // Create new, old should be freed

      // New instance starts with 0% coverage
      cov = cg_inst.get_inst_coverage();
      $display("  New instance coverage: %f", cov);
      if (cov != 0.0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
