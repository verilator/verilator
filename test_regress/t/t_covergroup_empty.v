// DESCRIPTION: Verilator: Verilog Test module - Edge case: empty covergroup
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

// Test: Empty covergroup (no coverpoints)
// Expected: Should compile, coverage should be 100% (nothing to cover)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [7:0] value;

   // Empty covergroup - no coverpoints defined
   covergroup cg_empty;
      // Intentionally empty
   endgroup

   cg_empty cg_inst = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      value <= value + 1;

      cg_inst.sample();

      if (cyc == 5) begin
         // Get coverage - should be 100% (nothing to fail)
         begin
            real cov;
            cov = cg_inst.get_inst_coverage();
            $display("Empty covergroup coverage: %f%%", cov);

            // Empty covergroup should report 100% coverage
            if (cov >= 99.9) begin
               $write("*-* All Finished *-*\n");
               $finish;
            end else begin
               $display("ERROR: Expected 100%% coverage for empty covergroup, got %f%%", cov);
               $stop;
            end
         end
      end

      if (cyc > 10) begin
         $display("ERROR: Test timed out");
         $stop;
      end
   end
endmodule
