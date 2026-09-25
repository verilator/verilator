// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Bins beyond the largest --coverage-max-bins, 4294967295 (2^32 - 1), and array bins of a
// real coverpoint beyond their own limit, --coverage-max-real-bins 2

module t;
  logic [31:0] data;
  real rdata;

  covergroup cg;
    // Warning (COVERIGN): array bins over the limit
    cp_array_over: coverpoint data {
      bins over_limit[] = {[0 : $]};
    }
    // Error: automatic bins over the limit
    cp_auto_over: coverpoint data {
      bins auto[33'd4294967296];
    }
    // Error: more bins in a coverpoint than the runtime indexes
    cp_total: coverpoint data {
      bins at_limit[] = {[0 : 32'hffff_fffe]};
      bins one = {0};
    }
    cp_real: coverpoint rdata {
      bins at_limit[] = {[1 : 2]};
      bins over_limit[] = {[1 : 3]};  // Warning (COVERIGN): 3 values
    }
  endgroup

  cg cg_inst = new;
  initial $finish;
endmodule
