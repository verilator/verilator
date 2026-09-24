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
  bit [63:0] wide;
  bit signed [7:0] sdata;

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

  // cg6: upper-open range {[$:hi]} == {[0:hi]} -> bins for 0 and 1
  covergroup cg6;
    cp: coverpoint sel {
      bins lo_open[] = {[$ : 1]};
    }
  endgroup

  // cg7: a reversed range {[hi:lo]} (hi<lo) contributes no bins; the plain
  // values 5 and 7 each create one bin -> 2 bins total.
  covergroup cg7;
    cp: coverpoint data {
      bins rev[] = {[3 : 1], 5, 7};
    }
  endgroup

  // cg8: wide (>= 64-bit) coverpoint, exercising the 64-bit domain-max path
  covergroup cg8;
    cp: coverpoint wide {
      bins w[] = {[0 : 1]};
    }
  endgroup

  // cg9: two ranges that are each under COVER_BINS_LIMIT (1048576) but whose
  // cumulative size exceeds it.  The first range populates the value list, the
  // second trips the running-total guard -> COVERIGN, the whole bin is ignored.
  // cpA is crossed, so the guard also runs for a cross-fed coverpoint.
  covergroup cg9;
    cpA: coverpoint wide {
      bins cumulative[] = {[0 : 600000], [0 : 600000]};
      bins ok = {5};
    }
    cpB: coverpoint sel {
      bins lo = {1};
    }
    cross cpA, cpB;
  endgroup

  // cg10: a signed range holds signed values: 7 bins for -3..3
  covergroup cg10;
    cp: coverpoint sdata {
      bins near_zero[] = {[-3 : 3]};
    }
  endgroup

  // cg11: a range holds only the values of the coverpoint type (IEEE 1800-2023 19.5.7):
  // 6 bins for 250..255
  covergroup cg11;
    cp: coverpoint data {
      bins top[] = {[250 : 260]};
    }
  endgroup

  // cg12: an intersect selects array elements by value: v[1] and v[2] hold 2 and 3
  covergroup cg12;
    cpX: coverpoint data {
      bins v[] = {[1 : 4]};
    }
    cpY: coverpoint sel {
      bins one = {1};
    }
    x: cross cpX, cpY{bins mid = binsof (cpX) intersect {[2 : 3]};}
  endgroup

  // cg13: [-1 : 3] holds only 0..3, like [0 : 3], so data 1 hits a[1], a[5] and b; each hit
  // also reaches the cross
  covergroup cg13;
    cp: coverpoint data {
      bins a[] = {[-1 : 3], [0 : 3]};
      bins b = {[0 : 3]};
    }
    cps: coverpoint sel {
      bins one = {1};
    }
    x: cross cp, cps;
  endgroup

  initial begin
    cg cg_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;
    cg4 cg4_inst;
    cg5 cg5_inst;
    cg6 cg6_inst;
    cg7 cg7_inst;
    cg8 cg8_inst;
    cg9 cg9_inst;
    cg10 cg10_inst;
    cg11 cg11_inst;
    cg12 cg12_inst;
    cg13 cg13_inst;

    cg_inst = new();
    cg2_inst = new();
    cg3_inst = new();
    cg4_inst = new();
    cg5_inst = new();
    cg6_inst = new();
    cg7_inst = new();
    cg8_inst = new();
    cg9_inst = new();
    cg10_inst = new();
    cg11_inst = new();
    cg12_inst = new();
    cg13_inst = new();

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

    // Hit cg6 upper-open bins ([$:1] == [0:1], 2 bins): cover 1 of 2
    sel = 0;
    cg6_inst.sample();
    `checkr(cg6_inst.get_inst_coverage(), 50.0);

    // Hit cg7 bins (reversed [3:1] -> no bins; 5 and 7 -> 2 bins): cover 1 of 2
    data = 5;
    cg7_inst.sample();
    `checkr(cg7_inst.get_inst_coverage(), 50.0);

    // Hit cg8 wide bins ([0:1], 2 bins): cover 1 of 2
    wide = 1;
    cg8_inst.sample();
    `checkr(cg8_inst.get_inst_coverage(), 50.0);

    // Exercise cg9 (crossed cpA with an ignored cumulative array bin)
    wide = 5;
    sel = 1;
    cg9_inst.sample();

    // Hit cg10 signed bins (-3..3, 7 bins): cover 2 of 7
    sdata = -3;
    cg10_inst.sample();
    sdata = 3;
    cg10_inst.sample();
    `checkr(cg10_inst.get_inst_coverage(), 100.0 * (2.0 / 7));

    // Hit cg11 clipped bins (250..255, 6 bins): cover 3 of 6
    data = 250;
    cg11_inst.sample();
    data = 252;
    cg11_inst.sample();
    data = 255;
    cg11_inst.sample();
    `checkr(cg11_inst.get_inst_coverage(), 50.0);

    // Hit cg12: data 3 is in the 'mid' cross bin, data 4 in an automatic cross bin
    sel = 1;
    data = 3;
    cg12_inst.sample();
    data = 4;
    cg12_inst.sample();

    // Hit cg13: three bins of cp at once
    sel = 1;
    data = 1;
    cg13_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
