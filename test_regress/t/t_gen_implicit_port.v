// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// An implicit net in a generate block is local to the block, even if an
// enclosing scope declares the name after the block (IEEE 1800-2023 6.10).

module sub (
    input logic [1:0] a,
    output logic y
);
  assign y = a[1];
endmodule

module t;
  import pkg::*;

  logic [1:0] y;
  logic [1:0] y_expr;
  logic [1:0] y_nested;
  logic y_if;
  logic [1:0] y_pkg;
  logic y_ga, y_gb;

  // verilator lint_off WIDTHEXPAND
  for (genvar p = 0; p < 2; p++) begin : g
    sub s (
        .a(x),
        .y(y[p])
    );
    // Also in an expression
    sub s_expr (
        .a(x_expr | 2'b00),
        .y(y_expr[p])
    );
    // Not in an enclosing scope: binds the package's x_pkg, even if declared later
    sub s_pkg (
        .a(x_pkg),
        .y(y_pkg[p])
    );
`ifdef T_LINT_IMPLICIT_GEN_BAD
    // Parameters are not nets: the later P is a reference before declaration
    sub s_param (
        .a(P),
        .y()
    );
`endif
  end

  if (1) begin : n
    for (genvar p = 0; p < 2; p++) begin : g
      sub s (
          .a(x_nested),
          .y(y_nested[p])
      );
    end
    logic [1:0] x_nested;
    assign x_nested = 2'b11;
  end

  if (1) begin : gi
    sub s (
        .a(x_if),
        .y(y_if)
    );
  end
  // verilator lint_on WIDTHEXPAND

  // No declaration at all: each block has its own x_blk
  if (1) begin : ga
    assign x_blk = 1'b1;
    sub s (
        .a({x_blk, 1'b0}),
        .y(y_ga)
    );
  end
  if (1) begin : gb
    sub s (
        .a({x_blk, 1'b0}),
        .y(y_gb)
    );
  end

  // Continuous assignment target
  if (1) begin : gw
    assign x_assign = 1'b1;
  end

  logic [1:0] x;
  logic [1:0] x_expr;
  logic [1:0] x_if;
  logic x_assign;
  localparam logic [1:0] P = 2'b11;
  assign x = 2'b11;
  assign x_expr = 2'b11;
  assign x_if = 2'b11;

  initial begin
    #1;
    if (x !== 2'b11) $stop;
    if (y_pkg !== 2'b11) $stop;
    if (y_ga !== 1'b1) $stop;
    if (ga.x_blk !== 1'b1) $stop;
    if (gw.x_assign !== 1'b1) $stop;
    // Undriven implicit nets (or undriven later declarations), never the driven value
    if (y === 2'b11) $stop;
    if (y_nested === 2'b11) $stop;
    if (y_if === 1'b1) $stop;
    if (y_expr === 2'b11) $stop;
    if (y_gb === 1'b1) $stop;
    if (x_assign === 1'b1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

package pkg;
  logic [1:0] x_pkg = 2'b11;
endpackage
