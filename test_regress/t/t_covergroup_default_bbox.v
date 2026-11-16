// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// With --bbox-unsup, a bin whose every value is unsupported holds no value.  It is not a default
// bin, and a default bin holds the values that it would.

module t;
  covergroup cg with function sample (bit [2:0] value);
    cp_bins: coverpoint value {
      bins low = {[0 : 1]};
      bins tolerance = {[5 +/- 1]};
      bins others = default;
    }
    cp_ignore: coverpoint value {
      bins low = {[0 : 1]};
      ignore_bins tolerance = {[5 +/- 1]};
      bins others = default;
    }
    cp_illegal: coverpoint value {
      bins low = {[0 : 1]};
      illegal_bins tolerance = {[5 +/- 1]};
    }
  endgroup

  cg inst = new;

  initial begin
    for (int i = 0; i < 8; ++i) inst.sample(3'(i));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
