// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test iff (enable) guard: sampling is gated by the enable condition.
// Covers iff on explicit value bins, default bin, array bins,
// simple 2-step transition, and 3-step transition.

module t;
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  logic enable;
  int value;

  // iff on explicit value bins
  covergroup cg_iff;
    cp_value: coverpoint value iff (enable) {
      bins disabled_lo = {1};
      bins disabled_hi = {2};
      bins enabled_lo  = {3};
      bins enabled_hi  = {4};
    }
  endgroup

  // iff on default bin
  covergroup cg_default_iff;
    cp: coverpoint value iff (enable) {
      bins known = {10};
      bins def = default;  // default bin with coverpoint-level iff
    }
  endgroup

  // iff on array bins
  covergroup cg_array_iff;
    cp: coverpoint value iff (enable) {
      bins arr[] = {5, 6, 7};  // array bins, all gated by iff
    }
  endgroup

  // iff on 2-step transition
  covergroup cg_trans2_iff;
    cp: coverpoint value iff (enable) {
      bins t2 = (1 => 2);
    }
  endgroup

  // iff on 3-step transition
  covergroup cg_trans3_iff;
    cp: coverpoint value iff (enable) {
      bins t3 = (1 => 2 => 3);
    }
  endgroup

  cg_iff          cg1 = new;
  cg_default_iff  cg2 = new;
  cg_array_iff    cg3 = new;
  cg_trans2_iff   cg4 = new;
  cg_trans3_iff   cg5 = new;

  initial begin
    // Sample disabled_lo and disabled_hi with enable=0 -- must not be recorded
    enable = 0;
    value = 1; cg1.sample();
    value = 2; cg1.sample();
    `checkr(cg1.get_inst_coverage(), 0.0);

    // Sample enabled_lo and enabled_hi with enable=1 -- must be recorded
    enable = 1;
    value = 3; cg1.sample();
    `checkr(cg1.get_inst_coverage(), 25.0);
    value = 4; cg1.sample();
    `checkr(cg1.get_inst_coverage(), 50.0);

    // cg2: default bin -- enable=1 lets known and default through
    enable = 1;
    value = 10; cg2.sample();  // hits 'known'
    `checkr(cg2.get_inst_coverage(), 50.0);
    value = 99; cg2.sample();  // hits 'def' (default)
    `checkr(cg2.get_inst_coverage(), 100.0);
    enable = 0;
    value = 99; cg2.sample();  // gated by iff -- must NOT hit 'def'
    `checkr(cg2.get_inst_coverage(), 100.0);

    // cg3: array bins with iff (3 bins: arr[5], arr[6], arr[7])
    // 1/3 hit -> 33.3% (not a clean binary fraction; no checkr)
    enable = 1;
    value = 5; cg3.sample();  // arr[5] hit
    enable = 0;
    value = 6; cg3.sample();  // gated

    // cg4: 2-step transition with iff
    enable = 1;
    value = 1; cg4.sample();
    `checkr(cg4.get_inst_coverage(), 0.0);
    value = 2; cg4.sample();  // (1=>2) hit with enable=1
    `checkr(cg4.get_inst_coverage(), 100.0);
    enable = 0;
    value = 1; cg4.sample();
    value = 2; cg4.sample();  // (1=>2) gated by iff
    `checkr(cg4.get_inst_coverage(), 100.0);

    // cg5: 3-step transition with iff
    enable = 1;
    value = 1; cg5.sample();
    value = 2; cg5.sample();  // mid-sequence, enable=1
    enable = 0;
    value = 3; cg5.sample();  // iff is disabled at step 3 - incomplete sequence is discarded
    `checkr(cg5.get_inst_coverage(), 0.0);
    enable = 1;
    value = 1; cg5.sample();
    value = 2; cg5.sample();
    value = 3; cg5.sample();  // (1=>2=>3) fully hit with enable=1
    `checkr(cg5.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
