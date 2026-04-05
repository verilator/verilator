// DESCRIPTION: Verilator: Verilog Test module
//
// Test covergroup where all bins are ignore_bins or illegal_bins (no regular
// bins). This exercises the totalBins==0 path in generateCoverageMethodBody()
// which returns 100.0 immediately.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [1:0] data;

  covergroup cg;
    cp: coverpoint data {
      ignore_bins  ign = {0, 1};
      illegal_bins ill = {2, 3};
      // No regular bins -> totalBins == 0 -> get_coverage returns 100.0
    }
  endgroup

  initial begin
    automatic cg cg_inst = new;

    // Only sample values that fall in ignore_bins, never illegal_bins
    data = 0; cg_inst.sample();
    data = 1; cg_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
