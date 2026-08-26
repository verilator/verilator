// DESCRIPTION: Verilator: VarXRef inlinedDots propagation regression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

module src #(
    parameter [3:0] VAL = 4'h0
) (
    output logic [3:0] val
);
  /*verilator no_inline_module*/
  assign val = VAL;
endmodule

module inner (
    input logic [3:0] in,
    output logic [3:0] out
);
  /*verilator inline_module*/
  assign out = in;
endmodule

module outer #(
    parameter [3:0] VAL = 4'h0
) (
    output logic [3:0] out
);
  /*verilator inline_module*/
  logic [3:0] s_val;
  src #(.VAL(VAL)) s (.val(s_val));
  // Use hierarchical ref s.val (not s_val) to test inlinedDots propagation
  inner u (
      .in(s.val),
      .out(out)
  );
endmodule

module t;
  logic [3:0] out0;
  logic [3:0] out1;
  logic [3:0] unused;

  // Top-level instance with the same name as the inlined one.
  src #(.VAL(4'hF)) s (.val(unused));

  outer #(.VAL(4'h1)) o0 (.out(out0));
  outer #(.VAL(4'h2)) o1 (.out(out1));

  initial begin
    if (out0 !== 4'h1) $stop;
    if (out1 !== 4'h2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
