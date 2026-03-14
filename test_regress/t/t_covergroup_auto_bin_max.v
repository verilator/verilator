// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test implicit auto-bin creation (no explicit bins) and option.auto_bin_max

module t;

  logic [2:0] data3;

  // Test 1: auto_bin_max default (64) - creates 8 bins for 3-bit signal
  covergroup cg1;
    cp_data3: coverpoint data3;
  endgroup

  // Test 2: auto_bin_max = 4 - creates 4 bins: [0:1],[2:3],[4:5],[6:7]
  covergroup cg2;
    option.auto_bin_max = 4;
    cp_data3: coverpoint data3;
  endgroup

  initial begin
    cg1 cg1_inst;
    cg2 cg2_inst;

    cg1_inst = new;
    cg2_inst = new;

    data3 = 0; cg1_inst.sample();
    data3 = 3; cg1_inst.sample();

    data3 = 0; cg2_inst.sample();
    data3 = 4; cg2_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
