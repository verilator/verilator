// DESCRIPTION: Verilator: Verilog Test module
//
// Negative test for the reference-cycle guard in V3Param's
// constifyMemberValue.  A class localparam whose value transitively
// references itself is reached through a `class::member` Dot in a cell
// parameter pin, so the fold recurses back into the same AstVar while it is
// still being resolved.  That must produce a clean user-facing error and
// leave a Const behind, NOT recurse forever or crash the following width
// pass on the still-unresolved Dot.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Self #(parameter int W = 1);
  localparam int a = a;
endclass

class Direct #(parameter int W = 1);
  // Two-step cycle: a -> b -> a
  localparam int a = b;
  localparam int b = a;
endclass

class Indirect #(parameter int W = 1);
  // Three-step cycle through sibling lparams: p -> q -> r -> p
  localparam int p = q;
  localparam int q = r;
  localparam int r = p;
endclass

module Sub #(parameter int P = 0) ();
endmodule

module t;
  typedef Self#(4) SCFG;
  typedef Direct#(4) DCFG;
  typedef Indirect#(4) ICFG;

  Sub #(SCFG::a) u_self ();
  Sub #(DCFG::a) u_direct ();
  Sub #(ICFG::p) u_indirect ();
endmodule
