// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A bins declaration may not redeclare a bin name of its coverpoint (IEEE 1800-2023 3.13)

module t;
  bit [3:0] v;
  covergroup cg;
    filtered: coverpoint v {
      bins a = {[0 : 3]} with (item > 1);
      bins a = {[4 : 7]} with (item > 5);  // <--- Bad: duplicate name
    }
    kinds: coverpoint v {
      bins a = {[0 : 3]};
      ignore_bins a = {[4 : 7]};  // <--- Bad: duplicate name
    }
    // Bin names are those of their coverpoint
    other: coverpoint v {
      bins a = {[0 : 3]};
    }
  endgroup
  cg inst = new;
  initial $finish;
endmodule
