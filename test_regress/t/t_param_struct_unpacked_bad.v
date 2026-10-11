// DESCRIPTION: Verilator: Verilog Test module
//
// An unpacked structure parameter override needs constant members, and a structure
// element of an array parameter can't be given an integer.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  int a;
  int b;
} s_t;

module m #(
    parameter s_t S[2] = '{default: '{a: 0, b: 0}}
) ();
endmodule

module t;
  int v = 1;
  localparam s_t G[2][2] = '{default: '{7, 8}};
  m #(.S('{'{a: 1, b: 2}, '{a: v, b: 4}})) i ();
endmodule
