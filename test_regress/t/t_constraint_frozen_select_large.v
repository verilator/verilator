// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A randomized index into a rand_mode(0)-capable table at the expansion
// limit must verilate: the frozen-select table nests by halving the index
// range, not one level per row.
class frozen_table;
  rand bit [7:0] frame[2];
  rand bit [7:0] target[16384][2];
  rand int idx;
  constraint c { idx == 16383; frame == target[idx]; }
endclass

module t;
  initial begin
    automatic frozen_table obj = new;
    automatic int ok;
    obj.target.rand_mode(0);
    ok = obj.randomize();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
