// DESCRIPTION: Verilator: Test transition bins - 3-value sequences
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic [2:0] state;
   int errors = 0;

   covergroup cg;
      cp_state: coverpoint state {
         bins trans_3val = (0 => 1 => 2);  // 3-value sequence
         bins trans_3val_2 = (2 => 3 => 4);  // Another 3-value sequence
      }
   endgroup

   cg cg_inst = new;

   initial begin
      // Test sequence 1: 0 => 1 => 2 (should complete trans_3val)
      state = 0;
      cg_inst.sample();

      state = 1;  // 0 => 1 (state machine now at position 1)
      cg_inst.sample();

      state = 2;  // 1 => 2 (completes trans_3val: 0=>1=>2)
      cg_inst.sample();

      // Test sequence 2: 2 => 3 => 4 (should complete trans_3val_2)
      state = 3;  // 2 => 3 (state machine now at position 1 for trans_3val_2)
      cg_inst.sample();

      state = 4;  // 3 => 4 (completes trans_3val_2: 2=>3=>4)
      cg_inst.sample();

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
