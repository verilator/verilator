// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [1:0] data;

   // Covergroup with 4 bins
   covergroup cg @(posedge clk);
      cp: coverpoint data {
         bins low  = {2'b00};
         bins mid1 = {2'b01};
         bins mid2 = {2'b10};
         bins high = {2'b11};
      }
   endgroup

   cg cg_inst = new;

   initial begin
      // Initially no bins covered - should be 0%
      real cov;
      cov = cg_inst.get_inst_coverage();
      $display("Coverage after 0 samples: %f", cov);
      if (cov != 0.0) $stop;

      // Cover 1 bin (low) - should be 25%
      @(posedge clk);
      data = 2'b00;
      @(posedge clk);
      cov = cg_inst.get_inst_coverage();
      $display("Coverage after 1/4 bins: %f", cov);
      if (cov < 24.9 || cov > 25.1) begin
         $display("%%Error: Expected 25%%, got %f", cov);
         $stop;
      end

      // Cover 2nd bin (mid1) - should be 50%
      @(posedge clk);
      data = 2'b01;
      @(posedge clk);
      cov = cg_inst.get_inst_coverage();
      $display("Coverage after 2/4 bins: %f", cov);
      if (cov < 49.9 || cov > 50.1) begin
         $display("%%Error: Expected 50%%, got %f", cov);
         $stop;
      end

      // Cover 3rd bin (mid2) - should be 75%
      @(posedge clk);
      data = 2'b10;
      @(posedge clk);
      cov = cg_inst.get_inst_coverage();
      $display("Coverage after 3/4 bins: %f", cov);
      if (cov < 74.9 || cov > 75.1) begin
         $display("%%Error: Expected 75%%, got %f", cov);
         $stop;
      end

      // Cover 4th bin (high) - should be 100%
      @(posedge clk);
      data = 2'b11;
      @(posedge clk);
      cov = cg_inst.get_inst_coverage();
      $display("Coverage after 4/4 bins: %f", cov);
      if (cov < 99.9 || cov > 100.1) begin
         $display("%%Error: Expected 100%%, got %f", cov);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
