// DESCRIPTION: Verilator: Verilog Test module
//
// Sibling-localparam recursion in V3Param's constifyMemberValue.  When a
// `class::member` Dot resolves to an lparam whose own value is not yet a
// Const because it references *sibling* lparams of the same class, those
// siblings must be folded first (deepest-first) so the whole chain
// constifies.  Covers values that reach the class::member Dot only
// indirectly, e.g. `one = base` where `base = Inner#(W)::v`, including
// multi-level chains and one expression referencing several siblings.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class Inner #(parameter int V = 1);
  localparam int v = V;
endclass

class C #(parameter int W = 1);
  // Only `base` holds the class::member Dot directly.
  localparam int base = Inner#(W)::v;
  // `one` is a bare VarRef to a sibling that is not yet Const.
  localparam int one = base;
  // Multi-level: two -> one -> base -> Inner::v
  localparam int two = one + 1;
  // One value referencing several not-yet-Const siblings at once.
  localparam int sum = base + one + two;
  // A non-param member: substituteParamMember must leave it alone.
  int notaparam;
endclass

module Sub #(
    parameter int P = 0
) ();
  localparam int GOT = P;
endmodule

module t;
  typedef C#(5) CFG;

  // Each pin drags a different point of the sibling chain through V3Param.
  Sub #(CFG::base) u_base ();
  Sub #(CFG::one) u_one ();
  Sub #(CFG::two) u_two ();
  Sub #(CFG::sum) u_sum ();

  initial begin
    `checkh(u_base.GOT, 32'd5);
    `checkh(u_one.GOT, 32'd5);
    `checkh(u_two.GOT, 32'd6);
    `checkh(u_sum.GOT, 32'd16);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
