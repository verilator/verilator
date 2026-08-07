// DESCRIPTION: Verilator: Verilog Test module
//
// Multi-level class hierarchies where one parameterized class's
// localparam value references another parameterized class via its
// own class-scope Dot (e.g. B::width = inner_a::v where inner_a is
// a typedef of A#(...)). resolveDotToTypedef must recursively resolve
// nested class::member Dots in a member's value before constifying,
// otherwise cell-pin deparam fails for the outer Dot.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module Sub #(
    parameter int WIDTH
) ();
endmodule

module t;
  // Two-level: B's lparam value contains a class::member Dot of its own
  virtual class A #(
      parameter int x
  );
    localparam int v = x * 2;
  endclass

  virtual class B #(
      parameter int y
  );
    typedef A#(y + 1) inner_a;
    localparam int width = inner_a::v;  // nested Dot inside B's lparam
  endclass

  // Three-level: C wraps B wraps A
  virtual class C #(
      parameter int z
  );
    typedef B#(z * 3) inner_b;
    localparam int total = inner_b::width;  // double-nested Dot
  endclass

  typedef B#(5) BInst;
  typedef C#(2) CInst;

  // (1) Standalone localparam - resolves via deferred-lparam path
  localparam int two_level = BInst::width;  // = A#(6)::v = 12
  localparam int three_level = CInst::total;  // = B#(6)::width = A#(7)::v = 14

  // (2) Cell pin uses the nested-class value directly - exercises the
  //     recursive Dot resolution inside resolveDotToTypedef
  Sub #(BInst::width) m_pin_direct ();
  Sub #(CInst::total) m_pin_deep ();
  Sub #(BInst::width + 1) m_pin_expr ();

  // (3) Cell pin chains through a deferred lparam whose value is
  //     itself a nested-class Dot
  localparam int chain = BInst::width;
  Sub #(chain) m_pin_chain ();

  initial begin
    `checkh(two_level, 32'd12);
    `checkh(three_level, 32'd14);
    `checkh(chain, 32'd12);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
