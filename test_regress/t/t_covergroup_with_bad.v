// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Invalid names in coverpoint bin 'with' filters (IEEE 1800-2023 19.5.1.1)

module t;
  bit [3:0] a, b;
  covergroup cg;
    aa: coverpoint a;
    // Only the coverpoint of the bin may be named
    bb: coverpoint b {
      bins x[] = aa with (item > 1);
    }
    // The candidate 'item' is only in the filter, not in the range list
    cc: coverpoint b {
      bins y[] = {[0 : item]} with (item > 1);
    }
  endgroup
  cg inst = new;
  initial $finish;
endmodule
