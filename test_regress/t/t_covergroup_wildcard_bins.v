// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test wildcard bins with don't care matching

module t;
  bit [7:0] data;

  covergroup cg;
    coverpoint data {
      // Match any value with upper nibble = 4'b0000
      wildcard bins low = {8'b0000_????};

      // Match any value with upper nibble = 4'b1111
      wildcard bins high = {8'b1111_????};

      // Match specific pattern with don't cares
      wildcard bins pattern = {8'b10?0_11??};

      // Non-wildcard range bin: [min:max] with min != max
      bins mid_range = {[8'h40 : 8'h4F]};

      // Wildcard bin using single-value range [5:5] (min==max, equivalent to a single value)
      wildcard bins wc_point = {[8'd5 : 8'd5]};
    }
  endgroup

  initial begin
    cg cg_inst;

    cg_inst = new();

    // Test low bin (upper nibble = 0000)
    data = 8'b0000_0101;  // Should match 'low'
    cg_inst.sample();

    // Test high bin (upper nibble = 1111)
    data = 8'b1111_1010;  // Should match 'high'
    cg_inst.sample();

    // Test pattern bin (10?0_11??)
    data = 8'b1000_1101;  // Should match 'pattern' (10[0]0_11[0]1)
    cg_inst.sample();

    // Verify another pattern match
    data = 8'b1010_1111;  // Should also match 'pattern' (10[1]0_11[1]1)
    cg_inst.sample();

    // Test mid_range bin: [0x40:0x4F]
    data = 8'h45;  // Should match 'mid_range'
    cg_inst.sample();

    // Test wc_point bin: exact value 5
    data = 8'd5;  // Should match 'wc_point'
    cg_inst.sample();

    // Verify non-matching value doesn't change coverage
    data = 8'b0101_0101;  // Shouldn't match any bin
    cg_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
