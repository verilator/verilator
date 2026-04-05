// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test default bins - catch-all for values not in other bins

// Non-covergroup class: exercises V3Active isCovergroup()=false branch
class DataHelper;
  bit [7:0] val;
  function new(bit [7:0] v); val = v; endfunction
endclass

module t;
  bit [7:0] data;
  logic [1:0] idx;
  logic [63:0] data64;   // 64-bit: exercises width>=64 auto-bin path (L139)
  logic [64:0] data65;   // 65-bit: exercises exprWidth>64 in makeRangeCondition
  DataHelper helper;     // Module-level class var: exercises V3Active isCovergroup()=false

  covergroup cg;
    coverpoint data {
      bins low = {[0:3]};
      bins high = {[12:15]};
      bins other = default;  // Catches everything else (4-11, 16+)
    }
  endgroup

  // Covergroup with default as the ONLY bin: exercises defaultCondp=BitTrue path
  covergroup cg2;
    cp_only_default: coverpoint data {
      bins all = default;
    }
  endgroup

  // Covergroup with default + ignore + illegal bins: exercises BINS_IGNORE/BINS_ILLEGAL
  // skip paths in generateDefaultBinMatchCode (L558-L559)
  covergroup cg3;
    coverpoint data {
      ignore_bins  bad = {255};    // BINS_IGNORE skip path
      illegal_bins err = {254};    // BINS_ILLEGAL skip path
      bins normal = {[1:10]};
      bins other = default;
    }
  endgroup

  // Covergroup with auto-bins + ignore_bins on small range: exercises L295 excluded-value continue
  // When numValidValues <= auto_bin_max, single-value auto-bins are created per value; the
  // excluded.find() check at L295 fires for the ignore_bins value (idx=2).
  covergroup cg4;
    cp_idx: coverpoint idx {
      ignore_bins skip = {2};  // value 2 excluded; auto-bins created for 0,1,3
    }
  endgroup

  // 64-bit signal with 4 auto-bins: exercises width>=64 branch in auto-bin range calculation
  covergroup cg5;
    cp_data64: coverpoint data64 { bins auto[4]; }
  endgroup

  // 65-bit signal with range bins: exercises exprWidth>64 path in makeRangeCondition
  covergroup cg6;
    cp_data65: coverpoint data65 { bins lo = {[0:15]}; bins hi = {[100:200]}; }
  endgroup

  // Unlabeled coverpoint: exercises cpName fallback via exprp()->name() (L1394-1398)
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

    // Hit high bin
    data = 14;
    cg_inst.sample();
    cg2_inst.sample();

    // Hit default bin with value 7 (not in low or high)
    data = 7;
    cg_inst.sample();
    cg2_inst.sample();

    // Hit another default value (should not increase coverage)
    data = 20;
    cg_inst.sample();
    cg2_inst.sample();

    // Sample cg3: exercises BINS_IGNORE/BINS_ILLEGAL skip in default-bin detection loop
    data = 2;   cg3_inst.sample();  // hits normal bin
    data = 7;   cg3_inst.sample();  // hits normal bin again
    data = 255; cg3_inst.sample();  // ignore_bins (not counted)
    // note: do not sample 254 (illegal_bins would cause runtime assertion)
    data = 100; cg3_inst.sample();  // hits default (other) bin

    // Sample cg4: exercises auto-bin generation with excluded value (L295)
    // idx=2 is in ignore_bins, so auto-bins cover 0,1,3 only
    idx = 0; cg4_inst.sample();
    idx = 1; cg4_inst.sample();
    idx = 3; cg4_inst.sample();

    // Sample cg5: 64-bit signal, sample into bin b[0] (value 0 is in first quarter)
    data64 = 0; cg5_inst.sample();
    data64 = 5; cg5_inst.sample();

    // Sample cg6: 65-bit signal with range bins
    data65 = 5;   cg6_inst.sample();  // hits bin lo=[0:15]
    data65 = 150; cg6_inst.sample();  // hits bin hi=[100:200]

    // Sample cg7: unlabeled coverpoint (exercises exprp()->name() path)
    data = 3;  cg7_inst.sample();  // hits bin lo
    data = 10; cg7_inst.sample();  // hits bin hi

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
