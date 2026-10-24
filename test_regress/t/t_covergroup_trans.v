// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test transition bins: simple 2-value, 3-value sequences, array bins,
// multi-value items in transition steps, the first sample, and sequences
// completing together.

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

  // The longest sequence supported, of 256 values
  covergroup cg_long with function sample (bit v);
    cp_long: coverpoint v {
      bins seq = (`SEQ256);
    }
  endgroup
  cg_long cg_long_inst = new;

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

    // cg_long: samples 0, 1, 0, ..., completing its sequence once
    for (int i = 0; i < 256; ++i) cg_long_inst.sample(1'(i));

    // cg_overlap: samples 1, 2, 1, 2, 1, 1, 1, 2
    begin
      automatic bit [1:0] samples[8] = '{1, 2, 1, 2, 1, 1, 1, 2};
      foreach (samples[i]) cg_overlap_inst.sample(samples[i]);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
