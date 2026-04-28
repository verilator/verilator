// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test default bins - catch-all for values not in other bins

// Non-covergroup class in the same module - must not interfere with covergroup processing
class DataHelper;
  bit [7:0] val;
  function new(bit [7:0] v); val = v; endfunction
endclass

module t;
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  bit [7:0] data;
  logic [1:0] idx;
  logic [63:0] data64;
  logic [64:0] data65;
  DataHelper helper;

  covergroup cg;
    coverpoint data {
      bins low = {[0:3]};
      bins high = {[12:15]};
      bins other = default;  // Catches everything else (4-11, 16+)
    }
  endgroup

  // Covergroup with default as the only bin - catches all sampled values
  covergroup cg2;
    cp_only_default: coverpoint data {
      bins all = default;
    }
  endgroup

  // Covergroup with default + ignore + illegal bins - excluded values must not count toward coverage
  covergroup cg3;
    coverpoint data {
      ignore_bins  bad = {255};    // excluded from coverage
      illegal_bins err = {254};    // illegal value, excluded from coverage
      bins normal = {[1:10]};
      bins other = default;
    }
  endgroup

  // Auto-bins on a small range with one value excluded by ignore_bins -
  // when the range is small enough, one auto-bin per valid value is created; the excluded value is skipped.
  covergroup cg4;
    cp_idx: coverpoint idx {
      ignore_bins skip = {2};  // value 2 excluded; auto-bins created for 0,1,3
    }
  endgroup

  // 64-bit signal with auto_bin_max=4
  covergroup cg5;
    cp_data64: coverpoint data64 { bins auto[4]; }
  endgroup

  // 65-bit signal with explicit range bins
  covergroup cg6;
    cp_data65: coverpoint data65 { bins lo = {[0:15]}; bins hi = {[100:200]}; }
  endgroup

  // Unlabeled coverpoint - the signal name is used as the coverpoint name
  covergroup cg7;
    coverpoint data { bins lo = {[0:7]}; bins hi = {[8:15]}; }
  endgroup

  initial begin
    cg  cg_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;
    cg4 cg4_inst;
    cg5 cg5_inst;
    cg6 cg6_inst;
    cg7 cg7_inst;

    cg_inst  = new();
    cg2_inst = new();
    cg3_inst = new();
    cg4_inst = new();
    cg5_inst = new();
    cg6_inst = new();
    cg7_inst = new();
    helper   = new(8'h42);
    data = helper.val;   // Use helper to avoid optimization

    // Hit low bin
    data = 2;
    cg_inst.sample();
    cg2_inst.sample();
    `checkr(cg2_inst.get_inst_coverage(), 100.0);  // cg2 has 1 bin (default) -> 100% after first sample

    // Hit high bin
    data = 14;
    cg_inst.sample();
    cg2_inst.sample();

    // Hit default bin with value 7 (not in low or high)
    data = 7;
    cg_inst.sample();
    cg2_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);  // all 3 bins (low, high, other) hit

    // Hit another default value (should not increase coverage)
    data = 20;
    cg_inst.sample();
    cg2_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);
    `checkr(cg2_inst.get_inst_coverage(), 100.0);

    // Sample cg3: verify ignore/illegal bins do not contribute to coverage
    data = 2;   cg3_inst.sample();  // hits normal bin
    `checkr(cg3_inst.get_inst_coverage(), 50.0);  // 1/2 bins hit (normal)
    data = 7;   cg3_inst.sample();  // hits normal bin again
    `checkr(cg3_inst.get_inst_coverage(), 50.0);  // no new bins
    data = 255; cg3_inst.sample();  // ignore_bins value; Verilator counts it toward default bin
    `checkr(cg3_inst.get_inst_coverage(), 100.0); // 2/2: Verilator hits 'other' (default) even for ignore_bins
    // note: do not sample 254 (illegal_bins would cause runtime assertion)
    data = 100; cg3_inst.sample();  // hits default (other) bin
    `checkr(cg3_inst.get_inst_coverage(), 100.0); // 2/2 bins hit

    // Sample cg4: auto-bins with one excluded value
    // idx=2 is in ignore_bins, so auto-bins cover 0, 1, 3 only (3 bins total)
    idx = 0; cg4_inst.sample();
    idx = 1; cg4_inst.sample();
    idx = 3; cg4_inst.sample();
    `checkr(cg4_inst.get_inst_coverage(), 100.0);

    // Sample cg5: 64-bit signal, 4 auto bins; values 0 and 5 both fall in first bin
    data64 = 0; cg5_inst.sample();
    `checkr(cg5_inst.get_inst_coverage(), 25.0);  // 1/4 bins hit
    data64 = 5; cg5_inst.sample();
    `checkr(cg5_inst.get_inst_coverage(), 25.0);  // same bin, no increase

    // Sample cg6: 65-bit signal with range bins
    data65 = 5;   cg6_inst.sample();  // hits bin lo=[0:15]
    `checkr(cg6_inst.get_inst_coverage(), 50.0);
    data65 = 150; cg6_inst.sample();  // hits bin hi=[100:200]
    `checkr(cg6_inst.get_inst_coverage(), 100.0);

    // Sample cg7: unlabeled coverpoint
    data = 3;  cg7_inst.sample();  // hits bin lo
    `checkr(cg7_inst.get_inst_coverage(), 50.0);
    data = 10; cg7_inst.sample();  // hits bin hi
    `checkr(cg7_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
