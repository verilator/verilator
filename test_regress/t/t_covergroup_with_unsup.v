// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unsupported 'with' filters: of wildcard patterns of more ranges of values than
// --coverage-max-bins 8, or distributed first

module t;
  bit [7:0] v;
  bit [1:0] t;
  bit [32:0] v33;
  covergroup cg;
    // The odd values are 128 ranges; the coverpoint is left without bins
    normal: coverpoint v {
      wildcard bins odd[] = {8'b???????1} with (1);
    }
    excluded: coverpoint v {
      bins low = {[0 : 3]};
      wildcard ignore_bins odd = {8'b???????1} with (item > 1);
    }
    // A cross selects the bins ignored as no bins
    mixed: coverpoint v {
      bins low = {[0 : 3]};
      wildcard bins odd[] = {8'b???????1} with (item > 1);
    }
    ct: coverpoint t;
    x: cross mixed, ct{bins sel = binsof (mixed.odd);}
  endgroup
  // Filters apply before values are distributed (IEEE 1800-2023 19.5.1.1)
  covergroup cg_first;
    type_option.distribute_first = 1;  // <--- Unsupported
    cp: coverpoint v {
      bins f[3] = {[0 : 5]} with (item < 3);
    }
  endgroup
  covergroup cg_default;
    type_option.distribute_first = 0;
    cp: coverpoint v {
      bins f[3] = {[0 : 5]} with (item < 3);
    }
  endgroup
  // Each is evaluated for at most 2**32 candidates, known when verilated
  covergroup cg_candidates;
    all: coverpoint v33 {
      bins b = all with (item < 5);  // <--- Unsupported: 2**33 candidates
    }
    listed: coverpoint v33 {
      bins b = {[0 : 33'h1_0000_0000]} with (item < 5);  // <--- Unsupported: 2**32 + 1
      // 2**32, as the values are evaluated once
      bins merged = {[0 : 33'h0_ffff_ffff], [0 : 33'h0_ffff_ffff]} with (item < 5);
      bins fixed[2] = {[0 : 33'h0_ffff_ffff], [0 : 33'h0_ffff_ffff]} with (item < 5);  // <--- Unsupported: 2**33
      bins at_limit = {[0 : 33'h0_ffff_ffff]} with (item < 5);
    }
  endgroup
  cg inst = new;
  cg_first first_inst = new;
  cg_candidates candidates_inst = new;
  cg_default default_inst = new;
  initial $finish;
endmodule
