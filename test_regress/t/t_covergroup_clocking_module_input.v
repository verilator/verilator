// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

// Test: Covergroup with clocking event using MODULE INPUT clock
// Status: WORKS - Verilator correctly auto-samples when clk is a module port

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [1:0] data;

   /* verilator lint_off UNSIGNED */
   covergroup cg @(posedge clk);
      cp: coverpoint data {
         bins val0 = {2'b00};
         bins val1 = {2'b01};
         bins val2 = {2'b10};
         bins val3 = {2'b11};
      }
   endgroup
   /* verilator lint_on UNSIGNED */

   cg cg_inst = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Change data each cycle
      data <= cyc[1:0];

      if (cyc == 5) begin
         /* verilator lint_off IMPLICITSTATIC */
         real cov = cg_inst.get_inst_coverage();
         /* verilator lint_on IMPLICITSTATIC */
         $display("Coverage: %0.1f%%", cov);

         // Should have hit all 4 bins (cycles 0-3) = 100%
         if (cov >= 99.0) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $display("ERROR: Expected 100%% coverage, got %f%%", cov);
            $stop;
         end
      end

      if (cyc > 10) begin
         $display("ERROR: Test timeout");
         $stop;
      end
   end

endmodule
