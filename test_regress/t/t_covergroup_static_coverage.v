// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test static get_coverage() with multiple instances

module t;

   covergroup cg;
      coverpoint data {
         bins low  = {[0:1]};
         bins mid  = {[2:3]};
         bins high = {[4:5]};
      }
   endgroup

   int data;

   initial begin
      cg cg1, cg2, cg3;
      real type_cov;

      cg1 = new;
      cg2 = new;
      cg3 = new;

      // Initially, no bins covered - should be 0%
      type_cov = cg::get_coverage();
      $display("Initial type coverage: %f", type_cov);
      if (type_cov != 0.0) $stop;

      // Sample cg1 with low bin
      data = 0;
      cg1.sample();
      type_cov = cg::get_coverage();
      $display("After cg1.sample(low): %f", type_cov);
      // 1 bin covered out of 3 = 33.33%
      if (type_cov < 33.0 || type_cov > 34.0) $stop;

      // Sample cg2 with mid bin
      data = 2;
      cg2.sample();
      type_cov = cg::get_coverage();
      $display("After cg2.sample(mid): %f", type_cov);
      // 2 bins covered out of 3 = 66.67%
      if (type_cov < 66.0 || type_cov > 67.0) $stop;

      // Sample cg3 with high bin
      data = 4;
      cg3.sample();
      type_cov = cg::get_coverage();
      $display("After cg3.sample(high): %f", type_cov);
      // 3 bins covered out of 3 = 100%
      if (type_cov < 99.9 || type_cov > 100.1) $stop;

      // Sample cg1 again with same bin - should not change coverage
      data = 1;
      cg1.sample();
      type_cov = cg::get_coverage();
      $display("After cg1.sample(low again): %f", type_cov);
      if (type_cov < 99.9 || type_cov > 100.1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
