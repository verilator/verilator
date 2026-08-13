// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A unique{} array slice wider than the pairwise-expansion size cap.

class WideRows;
  rand bit [7:0] wide[2][101];
  constraint c1 {foreach (wide[i]) unique {wide[i]};}
endclass

module t;
  initial begin
    automatic WideRows wr = new;
    void'(wr.randomize());
  end
endmodule
