// DESCRIPTION: Verilator: Verilog Test module
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Tests for invalid coverage option names

module t;
  logic [3:0] data;

  // Error: misspelled option.* name at covergroup level
  covergroup cg1;
    option.auto_bin_ma = 4;
    cp: coverpoint data;
  endgroup

  // Error: misspelled option.* name at coverpoint level
  covergroup cg2;
    cp: coverpoint data {
      option.at_lest = 2;
    }
  endgroup

  // Error: option.* name used under type_option.* (wrong namespace)
  covergroup cg3;
    type_option.auto_bin_max = 4;
    cp: coverpoint data;
  endgroup

  // Error: option.* name used under type_option.* at coverpoint level
  covergroup cg4;
    cp: coverpoint data {
      type_option.at_least = 2;
    }
  endgroup

  // Error: completely unknown type_option.* name
  covergroup cg5;
    type_option.bogus = 1;
    cp: coverpoint data;
  endgroup

  cg1 cg1_i = new;
  cg2 cg2_i = new;
  cg3 cg3_i = new;
  cg4 cg4_i = new;
  cg5 cg5_i = new;
  initial $finish;
endmodule
