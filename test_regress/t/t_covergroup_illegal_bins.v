// DESCRIPTION: Verilator: Verilog Test module
//
// Test that illegal_bins are excluded from coverage (like ignore_bins).
// Also tests coverpoints where all bins are ignore/illegal — get_coverage returns 100.0.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [1:0] data;
  logic [3:0] data4;

  covergroup cg;
    coverpoint data {
      bins low = {0};
      bins mid = {1};
      bins high = {2};
      illegal_bins forbidden = {3};
    }
  endgroup

  // cg2: illegal_bins on multi-step transitions and array notation
  covergroup cg2;
    cp_trans: coverpoint data4 {
      bins ok = {0};
      illegal_bins bad_2step = (1 => 2);       // 2-step illegal transition
      illegal_bins bad_3step = (1 => 2 => 3);  // multi-step illegal transition
      illegal_bins lib_default = default;       // illegal_bins = default
    }
    cp_arr: coverpoint data4 {
      bins ok = {0};
      illegal_bins bad_arr[] = {8, 9, 10};     // illegal array bins
      wildcard illegal_bins wlib = {4'b1?00};  // wildcard illegal bins
    }
  endgroup

  // cg3: all bins are ignore_bins or illegal_bins — get_coverage returns 100.0
  covergroup cg3;
    cp: coverpoint data {
      ignore_bins  ign = {0, 1};
      illegal_bins ill = {2, 3};
    }
  endgroup

  initial begin
    automatic cg  cg_inst  = new;
    automatic cg2 cg2_inst = new;
    automatic cg3 cg3_inst = new;

    // Sample legal values only
    data = 0; cg_inst.sample();
    data = 1; cg_inst.sample();
    data = 2; cg_inst.sample();

    // Sample cg2 - only safe values, never triggering illegal bins
    data4 = 0; cg2_inst.sample();

    // Sample cg3 - values that only hit ignore_bins, never illegal_bins
    data = 0; cg3_inst.sample();
    data = 1; cg3_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
