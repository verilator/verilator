// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test implicit auto-bin creation (no explicit bins) and option.auto_bin_max

module t;

  logic [2:0]  data3;
  logic [3:0]  data4;   // 4-bit signal for range-bin path tests
  logic [63:0] data64;  // 64-bit signal for width>=64 branch in createAutoBins

  // Test 1: auto_bin_max default (64) - creates 8 bins for 3-bit signal
  covergroup cg1;
    cp_data3: coverpoint data3;
  endgroup

  // Test 2: auto_bin_max = 4 at covergroup level - creates 4 bins: [0:1],[2:3],[4:5],[6:7]
  covergroup cg2;
    option.auto_bin_max = 4;
    cp_data3: coverpoint data3;
  endgroup

  // Test 3: auto_bin_max and at_least at *coverpoint* level (lines 207, 209)
  covergroup cg3;
    cp_data3: coverpoint data3 {
      option.auto_bin_max = 2;  // coverpoint-level: creates 2 bins [0:3],[4:7]
      option.at_least = 3;      // coverpoint-level at_least
    }
  endgroup

  // Test 4: range-bin skip path (lines 287, 356-359).
  // auto_bin_max=4 on 4-bit signal -> 4 range bins: [0:3],[4:7],[8:11],[12:15].
  // ignore_bins {[0:3]} excludes all values in the first range -> that bin is skipped.
  covergroup cg4;
    option.auto_bin_max = 4;
    cp: coverpoint data4 {
      ignore_bins ign = {[0:3]};  // first range excluded from coverage
    }
  endgroup

  // Test 5: 64-bit coverpoint exercises the width>=64 branches in createAutoBins
  // (V3Covergroup.cpp:269-270: maxVal/numTotalValues use UINT64_MAX sentinel)
  covergroup cg5;
    option.auto_bin_max = 4;
    cp_data64: coverpoint data64;
  endgroup

  // Test option.auto_bin_max at covergroup level: creates 4 bins [0:1],[2:3],[4:5],[6:7]
  covergroup cg6;
    option.auto_bin_max = 4;
    cp_data3: coverpoint data3;
  endgroup

  initial begin
    cg1 cg1_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;
    cg4 cg4_inst;
    cg5 cg5_inst;
    cg6 cg6_inst;

    cg1_inst = new;
    cg2_inst = new;
    cg3_inst = new;
    cg4_inst = new;
    cg5_inst = new;
    cg6_inst = new;

    data3 = 0; cg1_inst.sample();
    data3 = 3; cg1_inst.sample();

    data3 = 0; cg2_inst.sample();
    data3 = 4; cg2_inst.sample();

    data3 = 1; cg3_inst.sample();
    data3 = 5; cg3_inst.sample();

    // Sample valid (non-ignored) values for cg4
    data4 = 4;  cg4_inst.sample();  // [4:7] bin
    data4 = 8;  cg4_inst.sample();  // [8:11] bin
    data4 = 12; cg4_inst.sample();  // [12:15] bin

    // Sample cg5 (64-bit): exercises width>=64 path in createAutoBins
    data64 = 64'h0;                    cg5_inst.sample();
    data64 = 64'h1111111111111111;     cg5_inst.sample();
    data64 = 64'hffffffffffffffff;     cg5_inst.sample();

    data3 = 0; cg6_inst.sample();
    data3 = 7; cg6_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
