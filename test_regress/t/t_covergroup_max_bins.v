// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Bins declarations up to the largest --coverage-max-bins, 4294967295 (2^32 - 1), are
// accepted.  They are too many bins to simulate, so are only linted.

module t;
  logic [31:0] data;

  covergroup cg;
    cp_array: coverpoint data {
      bins at_limit[] = {[0 : 32'hffff_fffe]};
    }
    // Beyond a signed 32-bit size
    cp_auto: coverpoint data {
      bins auto[32'd4294967295];
    }
    cp_implicit: coverpoint data {
      option.auto_bin_max = 2147483647;
    }
  endgroup

  cg cg_inst = new;
  initial $finish;
endmodule
