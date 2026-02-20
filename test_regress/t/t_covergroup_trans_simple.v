// DESCRIPTION: Verilator: Test transition bins - simple two-value transitions
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [2:0] state;

   covergroup cg;
      cp_state: coverpoint state {
         bins trans1 = (0 => 1);
         bins trans2 = (1 => 2);
         bins trans3 = (2 => 3);
      }
   endgroup

   cg cg_inst = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
        0: state <= 0;
        1: state <= 1;  // 0 => 1 (trans1 should hit)
        2: state <= 2;  // 1 => 2 (trans2 should hit)
        3: state <= 3;  // 2 => 3 (trans3 should hit)
        4: begin
           $display("Coverage: %f%%", cg_inst.get_inst_coverage());
           if (cg_inst.get_inst_coverage() >= 99.0) begin  // Allow for rounding
              $write("*-* All Finished *-*\n");
              $finish;
           end else begin
              $display("ERROR: Expected 100%% coverage, got %f%%", cg_inst.get_inst_coverage());
              $stop;
           end
        end
      endcase

      // Sample the covergroup manually each clock
      cg_inst.sample();

      // Auto-stop after 10 cycles to prevent infinite loop
      if (cyc > 10) begin
         $display("ERROR: Test timed out");
         $stop;
      end
   end
endmodule
