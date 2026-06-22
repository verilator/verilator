// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test array bins - separate bin per value, including range expressions

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [7:0] data;
  bit [1:0] sel;

  covergroup cg;
    coverpoint data {
      // Array bins: creates 3 separate bins
      bins values[] = {1, 5, 9};

      // Non-array bin: creates 1 bin covering all values
      bins grouped = {2, 6, 10};
    }
  endgroup

  // cg2: array bins using a range expression - one bin per value in the range
  covergroup cg2;
    cp: coverpoint data {
      bins range_arr[] = {[0 : 3]};  // range expression: creates 4 separate bins
    }
  endgroup

  // cg3: sized array bins - bins r[N] = {[lo:hi]} distributes range into N bins
  covergroup cg3;
    cp: coverpoint data {
      bins range_sized[4] = {[4 : 7]};  // explicit count: 4 bins covering [4:7]
    }
  endgroup

  // cg4: array bins with '$' (open range) - '$' resolves to the coverpoint domain max.
  // For 2-bit sel, {[0:$]} == {[0:3]}: one bin per value -> 4 bins (issue #7750).
  covergroup cg4;
    cp: coverpoint sel {
      bins all_vals[] = {[0 : $]};
    }
  endgroup

  // cg5: lower-open range {[lo:$]} == {[lo:maxVal]} -> bins for 2 and 3
  covergroup cg5;
    cp: coverpoint sel {
      bins hi_vals[] = {[2 : $]};
    }
  endgroup

  initial begin
    cg cg_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;
    cg4 cg4_inst;
    cg5 cg5_inst;

    cg_inst = new();
    cg2_inst = new();
    cg3_inst = new();
    cg4_inst = new();
    cg5_inst = new();

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
    data = 0;
    cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 25.0);
    data = 1;
    cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 50.0);
    data = 2;
    cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 75.0);

    // Hit range_sized bins ([4:7])
    data = 4;
    cg3_inst.sample();
    `checkr(cg3_inst.get_inst_coverage(), 25.0);
    data = 5;
    cg3_inst.sample();
    `checkr(cg3_inst.get_inst_coverage(), 50.0);
    data = 6;
    cg3_inst.sample();
    `checkr(cg3_inst.get_inst_coverage(), 75.0);

    // Hit cg4 '$' bins ([0:$] == [0:3], 4 bins): cover 3 of 4
    sel = 0;
    cg4_inst.sample();
    `checkr(cg4_inst.get_inst_coverage(), 25.0);
    sel = 1;
    cg4_inst.sample();
    `checkr(cg4_inst.get_inst_coverage(), 50.0);
    sel = 2;
    cg4_inst.sample();
    `checkr(cg4_inst.get_inst_coverage(), 75.0);

    // Hit cg5 lower-open bins ([2:$] == [2:3], 2 bins): cover 1 of 2
    sel = 2;
    cg5_inst.sample();
    `checkr(cg5_inst.get_inst_coverage(), 50.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
