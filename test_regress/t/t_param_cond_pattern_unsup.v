// DESCRIPTION: Verilator: Verilog Test module
//
// Unsupported parameter overrides that use ?: to pick an assignment pattern.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic [2:0] a;
  logic [3:0] b;
} pk_t;

module m #(
    parameter int N = 1,
    parameter int V[N] = '{default: 0}
) ();
endmodule

module mp #(
    parameter logic [60:0] P = 0,
    parameter pk_t K = '0
) ();
endmodule

module t;
  localparam pk_t PK = '{a: 1, b: 2};
  localparam logic [60:0] ONES = '1;
  m #(.N(2), .V(1'bx ? '{1, 2} : '{3, 4})) i_x ();  // The condition's value is unknown
  // An operand of a real or packed type, which the conditional could convert
  mp #(.P(1 ? '{60: 1, 0: 1, default: 0} : 0.0)) i_real ();
  mp #(.P(1 ? ONES : '{default: 0})) i_vector ();
  mp #(.K(1 ? PK : '{a: 3, b: 4})) i_packed ();
endmodule
