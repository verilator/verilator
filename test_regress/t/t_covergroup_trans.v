// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test transition bins: simple 2-value, 3-value sequences, array bins,
// multi-value items in transition steps, the first sample, sequences
// completing together, overlapping matches, long sequences, and values
// resolved to the coverpoint's type.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// A sequence of 2^N alternating values 0, 1, 0, ...
`define SEQ2 0 => 1
`define SEQ4 `SEQ2 => `SEQ2
`define SEQ8 `SEQ4 => `SEQ4
`define SEQ16 `SEQ8 => `SEQ8
`define SEQ32 `SEQ16 => `SEQ16
`define SEQ64 `SEQ32 => `SEQ32
`define SEQ128 `SEQ64 => `SEQ64
`define SEQ256 `SEQ128 => `SEQ128
// verilog_format: on

module t;
  logic [2:0] state;

  covergroup cg;
    // Simple 2-value transitions
    cp_trans2: coverpoint state {
      bins trans1 = (0 => 1); bins trans2 = (1 => 2); bins trans3 = (2 => 3);
    }
    // 3-value sequence transitions
    cp_trans3: coverpoint state {
      bins seq_a = (0 => 1 => 2); bins seq_b = (2 => 3 => 4);
    }
    // Array bins: creates a separate bin per listed transition
    cp_array: coverpoint state {
      bins arr[] = (0 => 1), (1 => 2), (2 => 3);
    }
    // Multi-value item (comma list) in transition: matches 1 or 2 in second step
    cp_multi_item: coverpoint state {
      bins multi = (0 => 1, 2);  // second element is a two-value list
    }
    // Repetition-type bins: goto ([->N]) and non-consecutive ([=N]) repetition
    cp_reptype: coverpoint state {
      bins goto_bin = (0 => 1 [-> 2]);  // goto repetition - currently matched as simple (0=>1)
      bins noncons_bin = (2 [=1] => 3);  // non-consecutive repetition - currently matched as simple (2=>3)
    }
  endgroup

  // Coverpoint mixing a transition bin and a value-array bin: both route through the
  // VlCoverpoint runtime (the value array reports indexed as vals[0]..vals[N-1], like every
  // other array bin; the transition records into its own runtime bin).
  covergroup cg_array;
    cp_mix: coverpoint state {
      bins tr = (0 => 1);
      bins vals[] = {2, [4:5]};  // discrete + range elements
    }
  endgroup

  cg cg_inst = new;
  cg_array cg_array_inst = new;

  // No sample precedes the first, so it completes no transition, nor does the first sample
  // an iff guard enables (IEEE 1800-2023 19.5.2)
  covergroup cg_first with function sample (bit [2:0] v, bit en);
    cp_first: coverpoint v {
      bins rise = (0 => 1);
      bins stay = (2 => 2);  // Each 2 after a 2 completes it
      illegal_bins bad = (0 => 2);  // A hit stops the test
    }
    cp_gated: coverpoint v iff (en) {
      bins rise = (0 => 1);
      bins to2 = (0 => 2);
    }
  endgroup
  cg_first cg_first_inst = new;

  // A transition bin counts a sample once however many of its sequences complete there, so a
  // cross also sees the other bins the value hits
  covergroup cg_alt with function sample (bit [2:0] v, bit b);
    cp_two: coverpoint v {
      bins seq = (0 => 1), (0, 2 => 1);  // Both complete with 0, 1
      bins one = {1};
    }
    cp_multi: coverpoint v {
      bins seq = (1 => 2 => 3), (2 => 3), (0 => 1 => 2 => 3);  // All complete with 0, 1, 2, 3
      bins three = {3};
    }
    cp_b: coverpoint b;
    cx_two: cross cp_two, cp_b;
    cx_multi: cross cp_multi, cp_b;
  endgroup
  cg_alt cg_alt_inst = new;

  // Sequences of more than 64 values, which the runtime matches from tables of their values
  covergroup cg_long with function sample (bit [1:0] v, bit en);
    cp_long: coverpoint v iff (en) {
      bins gen64 = (`SEQ64);  // The longest sequence of generated matching
      bins seq = (`SEQ256 => 0);  // 257 values
      bins overlap = (`SEQ128);  // Its matches overlap
      bins alt = (`SEQ64 => 0, 1), (1 => 0);  // Complete together, counting once
      bins never = (`SEQ64 => 5);  // 5 is no 2-bit value: the bin leaves the report
      // Nor do bins with an item of only a range, which is ignored as unsupported
      // verilator lint_off COVERIGN
      bins range_short = (1 => [2 : 3]);
      bins range_long = (`SEQ64 => [2 : 3]);  // 65 values
    }
    // verilator lint_on COVERIGN
    // An ignored sequence, apart from the transition bins, from which other simulators remove the
    // transitions holding it (IEEE 1800-2023 19.5.5)
    cp_ignore: coverpoint v iff (en) {
      bins one = {1};
      ignore_bins ignore_long = (`SEQ128 => 0);  // 129 values
    }
  endgroup
  cg_long cg_long_inst = new;

  // Transition values resolve to the coverpoint's type, as bin values do, and one that it
  // cannot hold does not participate (IEEE 1800-2023 19.5.7): a sequence with an item of only
  // such values never matches, and a bin without a sequence that can leaves the report.
  localparam int NEG = -2;
  covergroup cg_signed with function sample (bit signed [3:0] v, longint l);
    cp_signed: coverpoint v {
      bins neg = (-1 => -2);
      bins neg_long = (`SEQ64 => -1);  // 65 values
      bins param = (`SEQ64 => NEG + 1);  // -1, as a parameter expression
      bins part = (15 => 0), (0 => 1);  // 15 is no 4-bit signed value
      bins none = (15 => 0);
      bins four_state = (4'b1x01 => 0);
    }
    cp_longint: coverpoint l {
      bins neg = (-1 => 0);
    }
  endgroup
  cg_signed cg_signed_inst = new;

  // A coverpoint of more than 64 bits
  covergroup cg_wide with function sample (bit [64:0] w);
    cp_wide: coverpoint w {
      bins rise = (0 => 1);
      bins top = (65'h1_0000_0000_0000_0000 => 1 => 0);
      bins long = (`SEQ64 => 0);  // 65 values, matched from a table
      bins long_top = (`SEQ64 => 65'h1_0000_0000_0000_0000, 2);
    }
  endgroup
  cg_wide cg_wide_inst = new;

  // Items of several values, out of order and repeated, on a signed four-state coverpoint
  covergroup cg_multi with function sample (logic signed [6:0] v);
    cp_multi: coverpoint v {
      bins multi = (-5, 9, -5 => -3, 3 => `SEQ64 => 7, -2, 63, -64, 7);  // 67 values
    }
  endgroup
  cg_multi cg_multi_inst = new;

  // Each instance matches a sequence from a table from its own samples
  covergroup cg_pair with function sample (bit [1:0] v);
    cp_pair: coverpoint v {
      bins long = (`SEQ64 => 2);  // 65 values
    }
  endgroup
  cg_pair cg_pair_a = new;
  cg_pair cg_pair_b = new;

  // Sequences matched from tables in crossed coverpoints, of which cp_dynamic, excluding a
  // value, gives its bins' values to the runtime.  binsof (IEEE 1800-2023 19.6.1) reads the last
  // value of each sequence that can match, and an ignored or illegal sequence excludes no value.
  covergroup cg_long_cross with function sample (bit [2:0] v, bit b);
    cp_static: coverpoint v {
      bins long = (`SEQ64 => 2);  // 65 values
      bins part = (`SEQ64 => 3), (9 => `SEQ64);  // 9 is no 3-bit value: only the first can match
      bins one = {1};
    }
    cp_dynamic: coverpoint v {
      bins long = (`SEQ64 => 2);
      bins part = (`SEQ64 => 3), (9 => `SEQ64);
      bins one = {1};
      bins five = {5};
      bins six = {6};
      ignore_bins ignored = {7};
      illegal_bins illegal_long = (`SEQ64 => 5);
      ignore_bins ignored_long = (`SEQ64 => 6);
    }
    cp_b: coverpoint b;
    x_static: cross cp_static, cp_b{
      bins twos = binsof (cp_static) intersect {2};
      bins ones = binsof (cp_static) intersect {1};
    }
    x_dynamic: cross cp_dynamic, cp_b{
      bins twos = binsof (cp_dynamic) intersect {2};
      bins ones = binsof (cp_dynamic) intersect {1};
    }
  endgroup
  cg_long_cross cg_long_cross_inst = new;

  // Sequences matched from tables on coverpoints of an enum, a packed struct, and a signed type
  // of 33 to 64 bits, of a last item of several values
  typedef enum bit [2:0] {
    ZERO,
    ONE,
    SIX = 6
  } digit_t;
  typedef struct packed {
    bit [3:0] tag;
    bit [35:0] data;
  } packet_t;
  covergroup cg_types with function sample (digit_t d, packet_t p, bit signed [39:0] s);
    cp_enum: coverpoint d {
      bins long = (`SEQ64 => SIX, ONE);  // 65 values
    }
    cp_struct: coverpoint p {
      bins long = (`SEQ64 => 40'h50_0000_0001);
    }
    cp_signed40: coverpoint s {
      bins long = (`SEQ64 => -1, 40'sh80_0000_0000);
    }
  endgroup
  cg_types cg_types_inst = new;

  // Overlapping matches of a sequence each count (IEEE 1800-2023 19.5.2)
  covergroup cg_overlap with function sample (bit [1:0] v);
    cp_overlap: coverpoint v {
      bins aba = (1 => 2 => 1);  // Samples 1 to 3, and 3 to 5
      bins aab = (1 => 1 => 2);  // Samples 6 to 8, after a partial match of 5 to 7
    }
  endgroup
  cg_overlap cg_overlap_inst = new;

  initial begin
    // Drive sequence 0->1->2->3->4 which hits all bins
    state = 0;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 0.0);
    state = 1;
    cg_inst.sample();  // 0=>1: trans1, seq_a pos1, arr[0=>1], multi
    state = 2;
    cg_inst.sample();  // 1=>2: trans2, seq_a done, arr[1=>2]
    state = 3;
    cg_inst.sample();  // 2=>3: trans3, seq_b pos1, arr[2=>3]
    state = 4;
    cg_inst.sample();  // 3=>4: seq_b done
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // cg_array: exercise the mixed transition + value-array coverpoint
    state = 0; cg_array_inst.sample();
    state = 1; cg_array_inst.sample();  // 0=>1: tr
    state = 2; cg_array_inst.sample();  // vals
    state = 3; cg_array_inst.sample();  // vals

    // cg_first: the first sample, of 2, is disabled in cp_gated
    cg_first_inst.sample(3'd2, 1'b0);  // Completes neither bad nor cp_gated's to2
    cg_first_inst.sample(3'd2, 1'b1);  // stay; cp_gated's first sample
    cg_first_inst.sample(3'd2, 1'b1);  // stay
    cg_first_inst.sample(3'd0, 1'b1);
    cg_first_inst.sample(3'd1, 1'b1);  // rise, in both coverpoints

    // cg_alt: samples 0, 1, 2, 3
    for (int i = 0; i < 4; ++i) cg_alt_inst.sample(3'(i), 1'b0);

    // cg_long: samples 0, 1, 0, ..., each followed by a disabled sample, which neither breaks
    // nor advances a sequence
    for (int i = 0; i < 257; ++i) begin
      cg_long_inst.sample(2'(i % 2), 1'b1);
      cg_long_inst.sample(2'd3, 1'b0);
    end
    // Every bin is hit but those without a sequence that can match, which count toward coverage
    // no more than the report
    `checkr(cg_long_inst.get_inst_coverage(), 100.0);

    // cg_signed
    cg_signed_inst.sample(-4'sd1, -1);
    cg_signed_inst.sample(-4'sd2, 0);  // neg, in both coverpoints
    for (int i = 0; i < 64; ++i) cg_signed_inst.sample(4'(i % 2), 0);  // 32 parts
    cg_signed_inst.sample(-4'sd1, 0);  // neg_long, param
    cg_signed_inst.sample(4'sd0, 0);  // Not 15 => 0, though -1 has 15's low bits
    // Every bin is hit but none and four_state, which count toward coverage no more than the
    // report
    `checkr(cg_signed_inst.get_inst_coverage(), 100.0);

    // cg_wide: 65'h1_0000_0000_0000_0001 is not 1, though its low bits are
    cg_wide_inst.sample(0);
    cg_wide_inst.sample(1);  // rise
    cg_wide_inst.sample(0);
    cg_wide_inst.sample(65'h1_0000_0000_0000_0001);
    cg_wide_inst.sample(65'h1_0000_0000_0000_0000);
    cg_wide_inst.sample(1);
    cg_wide_inst.sample(0);  // top
    for (int i = 0; i < 65; ++i) cg_wide_inst.sample(65'(i % 2));  // 32 rises, then long
    for (int i = 0; i < 64; ++i) cg_wide_inst.sample(65'(i % 2));  // 32 rises
    cg_wide_inst.sample(65'h1_0000_0000_0000_0002);  // Not 2, though its low bits are
    for (int i = 0; i < 64; ++i) cg_wide_inst.sample(65'(i % 2));  // 32 rises
    cg_wide_inst.sample(65'h1_0000_0000_0000_0000);  // long_top

    // cg_multi: six tries, of which the last two fail, as 4 is no value of the second item, nor
    // 8 of the last
    begin
      automatic logic signed [6:0] firsts[6] = '{9, -5, -5, 9, 9, -5};
      automatic logic signed [6:0] seconds[6] = '{-3, 3, 3, -3, 4, 3};
      automatic logic signed [6:0] lasts[6] = '{-64, 63, -2, 7, 7, 8};
      foreach (firsts[k]) begin
        cg_multi_inst.sample(firsts[k]);
        cg_multi_inst.sample(seconds[k]);
        for (int i = 0; i < 64; ++i) cg_multi_inst.sample(7'(i % 2));
        cg_multi_inst.sample(lasts[k]);
      end
    end

    // cg_pair: samples 0, 1, ... of a, between samples 3 of b, which break b's sequence alone
    for (int i = 0; i < 64; ++i) begin
      cg_pair_a.sample(2'(i % 2));
      cg_pair_b.sample(2'd3);
    end
    cg_pair_a.sample(2'd2);  // long
    cg_pair_b.sample(2'd2);
    `checkr(cg_pair_a.get_inst_coverage(), 100.0);
    `checkr(cg_pair_b.get_inst_coverage(), 0.0);

    // cg_long_cross: 0, 1, ... completing long, then part, all with b 0, then 5 and 6 with b 1
    for (int i = 0; i < 64; ++i) cg_long_cross_inst.sample(3'(i % 2), 1'b0);
    cg_long_cross_inst.sample(3'd2, 1'b0);
    for (int i = 0; i < 64; ++i) cg_long_cross_inst.sample(3'(i % 2), 1'b0);
    cg_long_cross_inst.sample(3'd3, 1'b0);
    cg_long_cross_inst.sample(3'd5, 1'b1);
    cg_long_cross_inst.sample(3'd6, 1'b1);

    // cg_types: three tries, each completing a sequence but with ZERO, a 1 without the tag, and
    // the largest value
    begin
      automatic digit_t digits[3] = '{SIX, ONE, ZERO};
      automatic packet_t packets[3] = '{40'h50_0000_0001, 40'h00_0000_0001, 40'h50_0000_0001};
      automatic bit signed [39:0] signeds[3] = '{-1, 40'sh80_0000_0000, 40'sh7f_ffff_ffff};
      foreach (digits[k]) begin
        for (int i = 0; i < 64; ++i) begin
          cg_types_inst.sample(digit_t'(i % 2), packet_t'(40'(i % 2)), 40'(i % 2));
        end
        cg_types_inst.sample(digits[k], packets[k], signeds[k]);
      end
    end

    // cg_overlap: samples 1, 2, 1, 2, 1, 1, 1, 2
    begin
      automatic bit [1:0] samples[8] = '{1, 2, 1, 2, 1, 1, 1, 2};
      foreach (samples[i]) cg_overlap_inst.sample(samples[i]);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
