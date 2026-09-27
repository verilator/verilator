// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test wildcard bins with don't care matching

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [7:0] data;
  bit [3:0] v;
  bit [1:0] v2;
  bit signed [3:0] sv;
  bit signed [1:0] sv2;
  bit [2:0] u;
  bit [99:0] w;
  longint l;

  covergroup cg;
    coverpoint data {
      // Match any value with upper nibble = 4'b0000
      wildcard bins low = {8'b0000_????};

      // Match any value with upper nibble = 4'b1111
      wildcard bins high = {8'b1111_????};

      // Match specific pattern with don't cares
      wildcard bins pattern = {8'b10?0_11??};

      // Non-wildcard range bin: [min:max] with min != max
      bins mid_range = {[8'h40 : 8'h4F]};

      // Wildcard bin using single-value range [5:5] (min==max, equivalent to a single value)
      wildcard bins wc_point = {[8'd5 : 8'd5]};
    }
  endgroup

  // Wildcard arrays: a bin for each value a pattern matches, named by the value (IEEE 1800-2023
  // 19.5.4, 19.5.1)
  covergroup cg_arrays;
    // The example of IEEE 1800-2023 19.5.4: 12..15
    ieee: coverpoint v {
      wildcard bins g12_15_array[] = {4'b11??};
    }
    // Values that are not consecutive: 8, 9, 12, 13
    gaps: coverpoint v {
      wildcard bins b[] = {4'b1?0?};
    }
    // A value two patterns match has one bin: 11..15
    dups: coverpoint v {
      wildcard bins b[] = {4'b11??, 4'b1?11};
    }
    // Patterns, values, and ranges: 0, 1, 5, 8, 9
    mixed: coverpoint v {
      wildcard bins b[] = {4'b000?, 5, [8 : 9]};
    }
    // Only values of the coverpoint type (IEEE 1800-2023 19.5.7): 1 and 12..15, and none
    wide: coverpoint v {
      wildcard bins keep[] = {8'b0000_11??, 8'b????_0001};
      wildcard bins none[] = {8'b1???_0000};
    }
    // Signed values: -1 and 1; -4..-1 of a signed pattern, none of a wider unsigned one, and
    // -8..-1 of one of the same width, cast to the coverpoint type
    sgn2: coverpoint sv2 {
      wildcard bins b[] = {2'sb?1};
    }
    sgn: coverpoint sv {
      wildcard bins ext[] = {8'sb1111_11??};
      wildcard bins none[] = {8'b1111_11??};
      wildcard bins cast[] = {4'b1???};
    }
    // Excluded values leave the array, 0 and 1, and a default bin holds the others: 4..6
    excl: coverpoint u {
      wildcard bins b[] = {3'b0??};
      wildcard ignore_bins i[] = {3'b00?};
      wildcard illegal_bins l[] = {3'b111};
      bins others = default;
    }
    // Excluded values also leave values that are not consecutive: 1 and 5
    split: coverpoint u {
      wildcard bins b[] = {3'b?0?};
      wildcard ignore_bins i[] = {3'b?00};
    }
    gated: coverpoint v {
      wildcard bins b[] = {4'b11?0} iff (v2 == 3);
    }
    nonzero: coverpoint v2 {
      wildcard bins b[] = {2'b1?};
    }
    // Crosses of wildcard arrays, one of whose bins are selected by value
    xx: cross nonzero, gaps{
      bins sel = binsof (gaps.b) intersect {[8 : 9]};
    }
    // Values beyond 64 bits: 16..31, and 24, 25, 28, 29
    wide100: coverpoint w {
      wildcard bins b[] = {100'h1?};
      wildcard bins f[] = {100'b1_1?0?};
    }
    ww: cross nonzero, wide100;
  endgroup

  // Sized wildcard arrays distribute the values in order, and retain duplicates (IEEE
  // 1800-2023 19.5.1)
  covergroup cg_sized;
    // <8,9>, <12,13>
    s: coverpoint v {
      wildcard bins b[2] = {4'b1?0?};
    }
    // <12,13,14>, <15,11,15>
    d: coverpoint v {
      wildcard bins b[2] = {4'b11??, 4'b1?11};
    }
  endgroup

  // Signed 64-bit values: a crossed array of negative ones, and those of a pattern with an x
  // sign bit, in value order
  covergroup cg_s64;
    neg: coverpoint l {
      wildcard bins b[] = {-1, -3};
    }
    top: coverpoint l {
      wildcard bins b[] = {64'sh?fff_ffff_ffff_fffe};
    }
    three: coverpoint v2 {
      bins b = {3};
    }
    nx: cross neg, three;
  endgroup

  cg_arrays arrays_inst = new;
  cg_sized sized_inst = new;
  cg_s64 s64_inst = new;

  initial begin
    cg cg_inst;

    cg_inst = new();

    // Test low bin (upper nibble = 0000)
    // Note: 8'b0000_0101 = 5 = 8'd5, so it matches BOTH 'low' and 'wc_point'
    data = 8'b0000_0101;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 40.0);  // 2/5: low + wc_point hit simultaneously

    // Test high bin (upper nibble = 1111)
    data = 8'b1111_1010;  // Should match 'high'
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 60.0);  // 3/5

    // Test pattern bin (10?0_11??)
    data = 8'b1000_1101;  // Should match 'pattern' (10[0]0_11[0]1)
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 80.0);  // 4/5

    // Verify another pattern match
    data = 8'b1010_1111;  // Should also match 'pattern' (10[1]0_11[1]1)
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 80.0);  // 4/5 - same bin, no increase

    // Test mid_range bin: [0x40:0x4F]
    data = 8'h45;  // Should match 'mid_range'
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);  // 5/5: all bins now hit

    // wc_point (value 5) was already hit in the first sample; confirm no regression
    data = 8'd5;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Verify non-matching value doesn't change coverage
    data = 8'b0101_0101;  // Shouldn't match any bin
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    for (int a = 0; a < 4; ++a) begin
      for (int i = 0; i < 16; ++i) begin
        v = 4'(i);
        sv = 4'(i);
        v2 = 2'(a);
        sv2 = 2'(a);
        u = 3'(i % 7);
        w = 100'(i + 16);
        arrays_inst.sample();
      end
      // With v2 == 0: all but sgn2, gated, nonzero, xx, and ww of the 14 items with bins
      if (a == 0) `checkr(arrays_inst.get_inst_coverage(), 100.0 * 9 / 14);
    end
    `checkr(arrays_inst.get_inst_coverage(), 100.0);

    v = 8;
    sized_inst.sample();
    `checkr(sized_inst.get_inst_coverage(), 100.0 * (1.0 / 2 + 0.0) / 2);
    v = 11;
    sized_inst.sample();
    `checkr(sized_inst.get_inst_coverage(), 100.0 * (1.0 / 2 + 1.0 / 2) / 2);
    v = 13;
    sized_inst.sample();
    `checkr(sized_inst.get_inst_coverage(), 100.0);

    v2 = 3;
    for (int i = 0; i < 16; ++i) begin
      l = {4'(i), 60'hfff_ffff_ffff_fffe};
      s64_inst.sample();
    end
    // All of top and three, none of neg and nx
    `checkr(s64_inst.get_inst_coverage(), 100.0 * 2 / 4);
    l = -1;
    s64_inst.sample();
    l = -3;
    s64_inst.sample();
    `checkr(s64_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
