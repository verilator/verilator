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

  covergroup cg;
    coverpoint data {
      bins low = {0};
      bins mid = {1};
      bins high = {2};
      illegal_bins forbidden = {3};
    }
  endgroup

  initial begin
    automatic cg cg_inst = new;

    // Sample legal values only
    data = 0;
    cg_inst.sample();

    data = 1;
    cg_inst.sample();

    data = 2;
    cg_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
