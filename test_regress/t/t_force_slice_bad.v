// DESCRIPTION: Verilator: Verilog Test module
//
// An unpacked array slice is not one of the left-hand sides IEEE 1800-2023
// 10.6.2 admits for force or release.  It is diagnosed rather than reaching
// V3Force with no variable reference at its base, which asserted internally.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [7:0] a[4];
  logic [7:0] fill[4];
  typedef struct {
    logic [7:0] arr[4];
  } s_t;
  s_t s;
  initial begin
    force a[1:2] = fill[1:2];
    release a[1:2];
    force s.arr[0:1] = fill[0:1];
    $finish;
  end
endmodule
