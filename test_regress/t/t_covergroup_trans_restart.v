// DESCRIPTION: Verilator: Test transition bins - restart behavior
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic [2:0] state;
   int errors = 0;

   covergroup cg;
      cp_state: coverpoint state {
         bins trans_restart = (1 => 2 => 3);  // Should handle restart correctly
      }
   endgroup

   cg cg_inst = new;

   initial begin
      // Sequence: 1, 2, 1, 2, 3
      // This tests restart logic: when we see 1 again while in middle of sequence,
      // we should restart from position 1 (not reset to 0)

      state = 1;  // Start: position = 1
      cg_inst.sample();
      $display("After state=1: seqpos should be 1");

      state = 2;  // Advance: position = 2
      cg_inst.sample();
      $display("After state=2: seqpos should be 2");

      state = 1;  // Restart! Should go to position 1 (not 0)
      cg_inst.sample();
      $display("After state=1 (restart): seqpos should be 1");

      state = 2;  // Advance: position = 2
      cg_inst.sample();
      $display("After state=2: seqpos should be 2");

      state = 3;  // Complete! Bin should increment
      cg_inst.sample();
      $display("After state=3: bin should have incremented, seqpos reset to 0");

      // Check coverage
      $display("Coverage: %f%%", cg_inst.get_inst_coverage());
      if (cg_inst.get_inst_coverage() < 99.0) begin
         $display("ERROR: Expected 100%% coverage, got %f%%", cg_inst.get_inst_coverage());
         errors++;
      end

      if (errors == 0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $display("*-* FAILED with %0d errors *-*", errors);
      end
      $finish;
   end

endmodule
