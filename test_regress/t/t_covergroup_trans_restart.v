// DESCRIPTION: Verilator: Test transition bins - restart behavior
// Known limitation: multi-value transition bins with restart semantics generate
// incomplete case statements; complex transitions are not fully supported.
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  logic [2:0] state;

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
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    state = 2;  // Advance: position = 2
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    state = 1;  // Restart! Should go to position 1 (not 0)
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    state = 2;  // Advance: position = 2
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    state = 3;  // Complete! Bin should increment
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
