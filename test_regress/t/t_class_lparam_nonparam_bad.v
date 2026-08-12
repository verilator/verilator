// DESCRIPTION: Verilator: Verilog Test module
//
// Negative test for the member-kind guard in V3Param's
// substituteParamMember.  A `class::member` Dot in a cell parameter pin
// that names a member which is not a parameter (a plain class property, or
// a static one) has no constant value to substitute, so V3Param must leave
// the Dot alone and let the normal unsupported-dotted-parameter diagnostic
// fire, rather than substituting or crashing.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class C #(parameter int W = 1);
  int notaparam;
  static int alsonotaparam;
  localparam int good = W;
endclass

module Sub #(parameter int P = 0) ();
endmodule

module t;
  typedef C#(4) CFG;

  Sub #(CFG::notaparam) u_prop ();
  Sub #(CFG::alsonotaparam) u_static ();
endmodule
