// DESCRIPTION: Verilator: Verilog Test module - Edge case: multiple instances
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

// Test: Multiple instances of same covergroup type sampling the same coverpoint
// Expected: Each instance tracks coverage independently, achieving same coverage
//           since they all sample the same expression (value1)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [2:0] value1;

   covergroup cg;
      cp: coverpoint value1 {
         bins low = {[0:3]};
         bins high = {[4:7]};
      }
   endgroup

   // Create three independent instances
   cg cg_inst1 = new;
   cg cg_inst2 = new;
   cg cg_inst3 = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
        0: begin
           value1 <= 1;  // low bin for all instances
        end
        1: begin
           value1 <= 6;  // high bin for all instances -> 100%
        end
        2: begin
           begin
              real cov1, cov2, cov3;
              cov1 = cg_inst1.get_inst_coverage();
              cov2 = cg_inst2.get_inst_coverage();
              cov3 = cg_inst3.get_inst_coverage();

              $display("Instance 1 coverage: %f%%", cov1);
              $display("Instance 2 coverage: %f%%", cov2);
              $display("Instance 3 coverage: %f%%", cov3);

              // All instances sample the same coverpoint (value1), so they should all be 100%
              // This tests that multiple instances track coverage independently,
              // even when sampling the same expression
              if (cov1 >= 99.0 && cov2 >= 99.0 && cov3 >= 99.0) begin
                 $write("*-* All Finished *-*\n");
                 $finish;
              end else begin
                 $display("ERROR: Coverage mismatch");
                 $display("  Expected: inst1=100%%, inst2=100%%, inst3=100%%");
                 $display("  Got: inst1=%f%%, inst2=%f%%, inst3=%f%%", cov1, cov2, cov3);
                 $stop;
              end
           end
        end
      endcase

      // Each instance samples the same value (value1)
      // But tracks coverage independently
      cg_inst1.sample();
      cg_inst2.sample();
      cg_inst3.sample();

      if (cyc > 10) begin
         $display("ERROR: Test timed out");
         $stop;
      end
   end
endmodule
