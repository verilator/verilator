// DESCRIPTION: Verilator: Verilog Test module
//
// A class localparam whose value is deferred (contains a class::member Dot)
// and also transitively references itself.  V3Param's deferred-lparam fold
// must break the reference cycle and report it cleanly, rather than
// recursing forever or leaving an unresolved Dot that reaches V3Width as an
// untyped node ("Node has no type" internal error).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module Sub #(parameter int WIDTH = 0) ();
endmodule

module t;
  virtual class A #(parameter int x = 0);
    localparam int v = x * 2;
  endclass

  virtual class B #(parameter int y = 0);
    typedef A#(y + 1) inner_a;
    // 'a' is deferred (holds the inner_a::v Dot) and also references 'b';
    // 'b' references 'a' back -> cycle through the deferred fold.
    localparam int a = inner_a::v + b;
    localparam int b = a;
  endclass

  typedef B#(5) BInst;

  Sub #(BInst::a) m ();
endmodule
