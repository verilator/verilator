// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test array bins - separate bin per value, including range expressions

module t;
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  bit [7:0] data;

  covergroup cg;
    coverpoint data {
      // Array bins: creates 3 separate bins
      bins values[] = {1, 5, 9};

      // Non-array bin: creates 1 bin covering all values
      bins grouped = {2, 6, 10};
    }
  endgroup

  // cg2: array bins using a range expression — one bin per value in the range
  covergroup cg2;
    cp: coverpoint data {
      bins range_arr[] = {[0:3]};   // range expression: creates 4 separate bins
    }
  endgroup

  // cg3: sized array bins — bins r[N] = {[lo:hi]} distributes range into N bins
  covergroup cg3;
    cp: coverpoint data {
      bins range_sized[4] = {[4:7]};  // explicit count: 4 bins covering [4:7]
    }
  endgroup

  initial begin
    cg  cg_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;

    cg_inst  = new();
    cg2_inst = new();
    cg3_inst = new();

    // Hit first array bin value (1)
    data = 1;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 25.0);

    // Hit second array bin value (5)
    data = 5;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 50.0);

    // Hit the grouped bin (covers all of 2, 6, 10)
    data = 6;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 75.0);

    // Hit third array bin value (9)
    data = 9;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Verify hitting other values in grouped bin doesn't increase coverage
    data = 2;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Hit range_arr bins ([0:3])
    data = 0; cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 25.0);
    data = 1; cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 50.0);
    data = 2; cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 75.0);

    // Hit range_sized bins ([4:7])
    data = 4; cg3_inst.sample();
    `checkr(cg3_inst.get_inst_coverage(), 25.0);
    data = 5; cg3_inst.sample();
    `checkr(cg3_inst.get_inst_coverage(), 50.0);
    data = 6; cg3_inst.sample();
    `checkr(cg3_inst.get_inst_coverage(), 75.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
