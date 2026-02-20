// DESCRIPTION: Verilator: Test transition bins - array bins
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [2:0] state;

   covergroup cg;
      // Test array bins: creates separate bin for each transition
      cp_array: coverpoint state {
         bins trans_array[] = (0 => 1), (1 => 2), (2 => 3);
      }
   endgroup

   cg cg_inst = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
        0: state <= 0;
        1: state <= 1;  // 0 => 1 (hits trans_array[0=>1])
        2: state <= 2;  // 1 => 2 (hits trans_array[1=>2])
        3: state <= 3;  // 2 => 3 (hits trans_array[2=>3])
        4: begin
           real cov = cg_inst.get_inst_coverage();
           $display("Coverage: %f%%", cov);
           // We should have hit all 3 array bins = 100%
           if (cov >= 99.0) begin
              $write("*-* All Finished *-*\n");
              $finish;
           end else begin
              $display("ERROR: Expected 100%% coverage, got %f%%", cov);
              $stop;
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
