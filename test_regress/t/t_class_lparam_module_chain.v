// DESCRIPTION: Verilator: Verilog Test module
//
// Module-instance parameter pins whose value chains through a
// class-scope-resolved localparam (typedef alias of a parameterized
// class, e.g. inst::b). V3LinkDot defers the inst::b Dot until
// post-V3Param; the cell deparam must follow VarRefs into any
// deferred lparam reachable from the pin tree and resolve its Dots
// inline so constify on the cell can fold.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Edmund Lam
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module Sub #(
    parameter int WIDTH
) ();
endmodule

// Two-level: outer module forwards its param to an inner cell, so the
// deferred lparam value must flow through the cell-deparam chain.
module SubL1 #(
    parameter int W
) ();
  Sub #(W) inner ();
endmodule

module t;
  virtual class C #(
      parameter int a
  );
    localparam int b = a;
  endclass

  typedef C#(4) c4;
  typedef C#(5) c5;
  typedef C#(8) c8;

  // Deferred lparams (value contains class::member Dot)
  localparam int b4 = c4::b;
  localparam int b5 = c5::b;
  localparam int b8 = c8::b;
  // Chained: value references another deferred lparam
  localparam int c8_ref = b8;
  localparam int d8_ref = c8_ref + 1;

  // Pin is bare VarRef to a deferred lparam
  Sub #(b8) m_bare ();
  // Pin chains through multiple deferred lparams (b8 -> c8_ref -> d8_ref)
  Sub #(d8_ref) m_chain ();
  // Pin is an expression mixing two deferred lparams
  Sub #(b4 + b5) m_expr ();
  // Pin mixes a Dot and a deferred lparam in the same expression
  Sub #(c4::b + b5) m_mix ();
  // Two-level: outer module forwards param to inner cell
  SubL1 #(b8) m_l1 ();

  initial begin
    `checkh(b4, 32'd4);
    `checkh(b5, 32'd5);
    `checkh(b8, 32'd8);
    `checkh(c8_ref, 32'd8);
    `checkh(d8_ref, 32'd9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
