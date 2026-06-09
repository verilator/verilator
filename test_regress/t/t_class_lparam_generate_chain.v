// DESCRIPTION: Verilator: Verilog Test module
//
// Generate-for / generate-if / generate-case conditions that reference
// a class-scope-resolved deferred localparam (e.g. inst::b). V3Param's
// visit(AstGenIf/Block/Case) calls V3Width::widthParamsEdit /
// constify on the cond/expr; the same transitive Dot-resolution used
// for cell pins must be applied here so the deferred lparam folds.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Edmund Lam
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Cell whose presence is observable, used inside generate blocks
// below to confirm each generate flavour elaborated the right way.
module Tag #(
    parameter int ID
) ();
  initial $write("Tag ID=%0d\n", ID);
endmodule

module t;
  virtual class C #(
      parameter int a
  );
    localparam int b = a;
  endclass

  typedef C#(3) c3;
  typedef C#(5) c5;

  // Deferred lparams
  localparam int b3 = c3::b;
  localparam int b5 = c5::b;

  // (1) Generate-for bound = deferred lparam
  for (genvar i = 0; i < b3; i++) begin : gf
    Tag #(100 + i) inst ();
  end

  // (2) Generate-if cond = deferred lparam
  if (b5 > b3) begin : gi_t
    Tag #(200) inst ();
  end else begin : gi_f
    Tag #(201) inst ();
  end

  // (3) Generate-case selector = deferred lparam
  case (b5)
    3: begin : gc Tag #(303) inst (); end
    5: begin : gc Tag #(305) inst (); end
    default: begin : gc Tag #(399) inst (); end
  endcase

  initial begin
    `checkh(b3, 32'd3);
    `checkh(b5, 32'd5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
