// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  integer i;
  integer j;
  wor [1:0] a;
  assign a = 2'b01;
  assign a[i] = 1'b1;
  wor [1:0] b;
  assign b[i] = 1'b1;
  assign b[j] = 1'b1;
  wor [3:0] c;
  assign c[1:0] = 2'b11;
  assign c[i] = 1'b1;
endmodule
