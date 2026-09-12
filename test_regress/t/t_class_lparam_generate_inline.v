// DESCRIPTION: Verilator: Verilog Test module
//
// Generate conditions that specialize a parameterized class *inline*
// (`C#(N)::b`, `$bits(C#(N))`) rather than through an intermediate
// localparam or typedef alias.
//
// V3Param's visit(AstGenIf/GenBlock/GenCase) iterates the condition
// before folding it, which queues the class reference in m_cellps via
// visitCellOrClassRef.  Folding then destroys those nodes outright
// (V3Width deletes a resolved $bits() tree; the untaken arm is
// deleteTree()'d) instead of deferring via pushDeletep, so the queued
// pointers must be dropped or processWorkQ()'s drain loop dereferences
// freed memory -- giving a bogus "Expected module parameterization"
// fatal, or a segfault on the generate-case flavour.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package P;
  virtual class cfg #(
      parameter int W = 8
  );
    localparam int width = W;
    typedef logic [W-1:0] data_t;
  endclass
endpackage

// Cell whose presence is observable, to confirm each generate
// flavour elaborated the arm we expect.
module Tag #(
    parameter int ID
) ();
  initial $write("Tag ID=%0d\n", ID);
endmodule

module t;
  // Class in the compilation unit, reached with a single '::'
  virtual class C #(
      parameter int a
  );
    localparam int b = a;
  endclass

  // (1) Generate-if cond: inline specialization, single '::'
  if (C#(5)::b > C#(3)::b) begin : gi_t
    Tag #(200) inst ();
  end else begin : gi_f
    Tag #(201) inst ();
  end

  // (2) Generate-if cond: inline specialization through a package, two '::'
  if (P::cfg#(12)::width == 12) begin : gi_pkg
    Tag #(212) inst ();
  end

  // (3) Generate-if cond: $bits() of an inline specialization.  No Dot at
  // all -- the queued node is the AstClassRefDType itself, and V3Width
  // deletes the whole $bits() tree once it folds.
  if ($bits(P::cfg#(6)::data_t) == 6) begin : gi_bits
    Tag #(206) inst ();
  end

  // (4) Genvar bound = inline specialization
  for (genvar i = 0; i < C#(3)::b; i++) begin : gf
    Tag #(100 + i) inst ();
  end

  // (5) Generate-case selector = inline specialization
  case (P::cfg#(5)::width)
    3: begin : gc Tag #(303) inst (); end
    5: begin : gc Tag #(305) inst (); end
    default: begin : gc Tag #(399) inst (); end
  endcase

  initial begin
    `checkh(C#(3)::b, 32'd3);
    `checkh(P::cfg#(12)::width, 32'd12);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
