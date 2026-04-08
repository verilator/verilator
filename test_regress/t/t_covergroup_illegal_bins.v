// DESCRIPTION: Verilator: Verilog Test module
//
// Test that illegal_bins are excluded from coverage (like ignore_bins)
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

  // cg2: exercises illegal_bins with 3-step transition (lines 744-747) and
  //      illegal_bins array notation (lines 996-998)
  covergroup cg2;
    cp_trans: coverpoint data4 {
      bins ok = {0};
      illegal_bins bad_2step = (1 => 2);       // 2-step illegal transition (simple path)
      illegal_bins bad_3step = (1 => 2 => 3);  // multi-step illegal transition
      illegal_bins lib_default = default;       // illegal_bins = default (L7123-7124)
    }
    cp_arr: coverpoint data4 {
      bins ok = {0};
      illegal_bins bad_arr[] = {8, 9, 10};     // illegal array bins
      wildcard illegal_bins wlib = {4'b1?00};  // wildcard illegal bins (L7087-7088)
    }
  endgroup

  initial begin
    automatic cg  cg_inst  = new;
    automatic cg2 cg2_inst = new;

    // Sample legal values only
    data = 0; cg_inst.sample();
    data = 1; cg_inst.sample();
    data = 2; cg_inst.sample();

    // Sample cg2 - only safe values, never triggering illegal bins
    data4 = 0; cg2_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
