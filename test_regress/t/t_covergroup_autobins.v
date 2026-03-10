// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test automatic bin creation when coverpoint has no explicit bins

module t(/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  logic [2:0] data3;  // 3-bit: values 0-7
  logic [1:0] data2;  // 2-bit: values 0-3

  // Test 1: auto_bin_max default (64) - should create 8 bins for 3-bit signal
  // Each value should get its own bin since 2^3 = 8 < 64
  covergroup cg1;
    cp_data3: coverpoint data3;  // No bins specified - autobins
  endgroup

  // Test 2: With option.auto_bin_max = 4
  // Should create 4 bins: [0:1], [2:3], [4:5], [6:7]
  covergroup cg2;
    option.auto_bin_max = 4;
    cp_data3: coverpoint data3;  // No bins specified - autobins
  endgroup

  // Test 3: With ignore bins - should still auto-create for non-ignored values
  // Autobins created, but value 7 is ignored
  covergroup cg3;
    cp_data3: coverpoint data3 {
      ignore_bins reserved = {7};
    }
  endgroup

  // Test 4: Smaller signal - 2-bit
  // Should create 4 bins (one per value) since 2^2 = 4 < 64
  covergroup cg4;
    cp_data2: coverpoint data2;  // No bins specified - autobins
  endgroup

  // Test 5: With auto_bin_max smaller than signal range
  // 2-bit signal (0-3) with auto_bin_max=2 should create 2 bins: [0:1], [2:3]
  covergroup cg5;
    option.auto_bin_max = 2;
    cp_data2: coverpoint data2;  // No bins specified - autobins
  endgroup

  initial begin
    cg1 cg1_inst;
    cg2 cg2_inst;
    cg3 cg3_inst;
    cg4 cg4_inst;
    cg5 cg5_inst;

    cg1_inst = new;
    cg2_inst = new;
    cg3_inst = new;
    cg4_inst = new;
    cg5_inst = new;

    // Test CG1: Hit values 0, 1, 2 (3 of 8 bins = 37.5%)
    data3 = 0; cg1_inst.sample();
    data3 = 1; cg1_inst.sample();
    data3 = 2; cg1_inst.sample();

    // Test CG2: Hit values 0, 1, 4 (bins [0:1] and [4:5], 2 of 4 bins = 50%)
    data3 = 0; cg2_inst.sample();
    data3 = 1; cg2_inst.sample();
    data3 = 4; cg2_inst.sample();

    // Test CG3: Hit values 0, 1, 7 (7 is ignored, so 2 of 7 valid bins = 28.6%)
    data3 = 0; cg3_inst.sample();
    data3 = 1; cg3_inst.sample();
    data3 = 7; cg3_inst.sample();  // Ignored

    // Test CG4: Hit all values 0-3 (4 of 4 bins = 100%)
    data2 = 0; cg4_inst.sample();
    data2 = 1; cg4_inst.sample();
    data2 = 2; cg4_inst.sample();
    data2 = 3; cg4_inst.sample();

    // Test CG5: Hit values 0, 3 (bins [0:1] and [2:3], 2 of 2 bins = 100%)
    data2 = 0; cg5_inst.sample();
    data2 = 3; cg5_inst.sample();

    $display("CG1 (8 autobins): %0.1f%%", cg1_inst.get_inst_coverage());
    $display("CG2 (4 autobins w/ option): %0.1f%%", cg2_inst.get_inst_coverage());
    $display("CG3 (7 autobins w/ ignore): %0.1f%%", cg3_inst.get_inst_coverage());
    $display("CG4 (4 autobins): %0.1f%%", cg4_inst.get_inst_coverage());
    $display("CG5 (2 autobins w/ option): %0.1f%%", cg5_inst.get_inst_coverage());

    // Validate coverage results
    `checkr(cg1_inst.get_inst_coverage(), 37.5);
    `checkr(cg2_inst.get_inst_coverage(), 50.0);
    `checkr(cg3_inst.get_inst_coverage(), 100.0 * (2.0/7.0));
    `checkr(cg4_inst.get_inst_coverage(), 100.0);
    `checkr(cg5_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
