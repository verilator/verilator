// DESCRIPTION: Verilator: Verilog Test module
//
// Errors for an unpacked array parameter whose size comes from another
// parameter of the same instantiation.  See issue #5890.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

module m #(
    parameter int N = 0,
    parameter int V[N] = '{}
) ();
endmodule

// Size defaults to zero, so an instance must override it
module z #(
    parameter int N = 0,
    parameter int V[N] = '{default: 0}
) ();
endmodule

// Size from parameters whose defaults refer to each other
module cy #(
    parameter int N = M,
    parameter int M = N,
    parameter int V[N] = '{default: 0}
) ();
endmodule

// Scalar width from parameters whose defaults refer to each other
module cs #(
    parameter int N = M,
    parameter int M = N,
    parameter logic [N-1:0] P = '0
) ();
endmodule

// Type from parameters whose defaults refer to each other
module ct #(
    parameter type T = logic [W-1:0],
    parameter int W = $bits(T),
    parameter T V[2] = '{default: 0}
) ();
endmodule

// Types from typedefs that refer to each other, directly or through a value
module ctd;
  typedef A;
  typedef logic [$bits(A)-1:0] B;
  typedef B A;
  parameter A V[2] = '{default: 0};
endmodule
module ctv;
  typedef A;
  parameter int W = $bits(A);
  typedef logic [W-1:0] A;
  parameter A V[2] = '{default: 0};
endmodule

// Width from a parameter whose override isn't a constant, given after the value
module wx #(
    parameter int N = 1,
    parameter logic [N-1:0] P = '0
) ();
endmodule

// Size from a parameter that is never given a value
module nv #(
    parameter int N,
    parameter int V[N] = '{default: 0}
) ();
endmodule

// Type from a type parameter that is never given a type
module nt #(
    parameter type T,
    parameter T V[2] = '{default: 0}
) ();
endmodule

module t;
  int x;
  m #(.N(3), .V('{1, 2})) i_few ();  // Too few elements
  m #(.N(2), .V('{1, 2, 3})) i_many ();  // Too many elements
  z i_zero ();  // Size left at its zero default
  cy #(.V('{1})) i_cy ();
  cs #(.P(1)) i_cs ();
  ct #(.V('{1, 0})) i_ct ();
  ctd #(.V('{1, 0})) i_ctd ();
  ctv #(.V('{1, 0})) i_ctv ();
  wx #(.P(1), .N(x)) i_wx ();
  nv #(.V('{1, 2})) i_nv ();
  nt #(.V('{1, 2})) i_nt ();
endmodule
