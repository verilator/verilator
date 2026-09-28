// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Invalid types of coverpoint bin 'with' filters (IEEE 1800-2023 19.5.1.1)

module t;
  real r;
  bit [3:0] a;
  string s = "x";
  covergroup cg;
    // Not allowed for a real coverpoint, nor other non-integral ones
    rr: coverpoint r {
      bins b = {[0 : 3]} with (item > 1);
    }
    ss: coverpoint s {
      bins b = {"a"} with (1);
    }
    // The result must be assignment compatible with an integral type
    aa: coverpoint a {
      bins b[] = {[0 : 3]} with (s);
    }
  endgroup
  cg inst = new;
  initial $finish;
endmodule
