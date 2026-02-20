// DESCRIPTION: Verilator: Test automatic sampling with clocking events
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [1:0] data;

   // Covergroup with automatic sampling on posedge clk
   covergroup cg @(posedge clk);
      cp_data: coverpoint data {
         bins zero  = {2'b00};
         bins one   = {2'b01};
         bins two   = {2'b10};
         bins three = {2'b11};
      }
   endgroup

   cg cg_inst = new;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
        0: data <= 2'b00;  // Hit bin zero
        1: data <= 2'b01;  // Hit bin one
        2: data <= 2'b10;  // Hit bin two
        3: data <= 2'b11;  // Hit bin three
        4: begin
           $display("Coverage: %f%%", cg_inst.get_inst_coverage());
           if (cg_inst.get_inst_coverage() >= 99.0) begin
              $write("*-* All Finished *-*\n");
              $finish;
           end else begin
              $display("ERROR: Expected 100%% coverage, got %f%%", cg_inst.get_inst_coverage());
              $stop;
           end
        end
      endcase

      // NOTE: NO manual .sample() call - relying on automatic sampling!

      // Auto-stop after 10 cycles to prevent infinite loop
      if (cyc > 10) begin
         $display("ERROR: Test timed out");
         $stop;
      end
   end
endmodule
