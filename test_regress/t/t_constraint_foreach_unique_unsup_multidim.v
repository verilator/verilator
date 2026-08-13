// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A row of a 3-D array is itself a 2-D slice, not the 1-D slice this
// unique{} path supports. A row that is itself a queue, dynamic array,
// associative array, or wildcard array is unsupported for the same reason.

class Cube;
  rand bit [4:0] cube[2][3][3];
  constraint c1 {foreach (cube[i]) unique {cube[i]};}
endclass

class RowKinds;
  rand bit [4:0] queue_rows[3][2][$];
  rand bit [4:0] dynarr_rows[3][2][];
  rand bit [4:0] assoc_rows[3][2][int];
  rand bit [4:0] wild_rows[3][2][*];
  constraint c1 {foreach (queue_rows[i]) unique {queue_rows[i]};}
  constraint c2 {foreach (dynarr_rows[i]) unique {dynarr_rows[i]};}
  constraint c3 {foreach (assoc_rows[i]) unique {assoc_rows[i]};}
  constraint c4 {foreach (wild_rows[i]) unique {wild_rows[i]};}
endclass

module t;
  initial begin
    automatic Cube cb = new;
    automatic RowKinds rk = new;
    void'(cb.randomize());
    void'(rk.randomize());
  end
endmodule
