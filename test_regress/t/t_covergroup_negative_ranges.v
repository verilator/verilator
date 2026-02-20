// DESCRIPTION: Verilator: Verilog Test module - Edge case: negative value ranges
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

// Test: Bins with negative value ranges
// Expected: Should handle negative numbers correctly

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int signed value;

   /* verilator lint_off CMPCONST */
   covergroup cg;
      cp_neg: coverpoint value {
         bins negative = {[-100:-1]};
         bins zero = {0};
         bins positive = {[1:100]};
         bins mixed = {[-10:10]};
      }
   endgroup
   /* verilator lint_on CMPCONST */

   cg cg_inst = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
        0: value <= -50;    // Hit negative bin
        1: value <= 0;      // Hit zero bin
        2: value <= 50;     // Hit positive bin
        3: value <= -5;     // Hit mixed bin (also negative)
        4: value <= 5;      // Hit mixed bin (also positive)
        5: begin
           begin
              real cov;
              cov = cg_inst.get_inst_coverage();
              $display("Coverage with negative ranges: %f%%", cov);

              // All 4 bins should be hit = 100%
              if (cov >= 99.0) begin
                 $write("*-* All Finished *-*\n");
                 $finish;
              end else begin
                 $display("ERROR: Expected 100%% coverage, got %f%%", cov);
                 $stop;
              end
           end
        end
      endcase

      cg_inst.sample();

      if (cyc > 10) begin
         $display("ERROR: Test timed out");
         $stop;
      end
   end
endmodule
