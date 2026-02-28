// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input wire [3:0] a,
  input wire [3:0] b,
  input wire [3:0] c,
  output wire [10:0] o
);
  wire [ 3:0]  x = ~a & ~b;
  wire [ 3:0]  y = ~b & ~c;
  wire [ 3:0]  z = ~c & ~a;
  wire [ 0:0] w1 = x[0];
  wire [ 7:0] w8 = {8{x[1]}};
  wire [15:0] w16 = {2{w8}};
  wire [31:0] w32 = {2{w16}};
  wire [63:0] w64a = {2{w32}};
  wire [63:0] w64b = {2{~w32}};
  wire [62:0] w63 = 63'({2{~w32}});
  wire [95:0] w96 = 96'(w64a);

  assign o = {^x, ^y, ^z, ^w1, ^w8, ^w16, ^w32, ^w64a, ^w64b, ^w63, ^w96};
endmodule
