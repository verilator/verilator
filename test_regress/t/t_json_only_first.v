// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Outputs
    q,
    // Inputs
    clk,
    d
);
  input clk;
  input [3:0] d;
  output wire [3:0] q;

  logic [3:0] between;
  logic direct_named;
  logic computed_named;
  logic anonymous_expr;

  localparam logic [1:0] S_IDLE = 2'b00;
  localparam logic [1:0] S_FETCH = 2'b01;
  localparam logic [1:0] S_EXEC = S_FETCH + 1;

  assign direct_named = d[1:0] == S_IDLE;
  assign computed_named = d[1:0] == S_EXEC;
  assign anonymous_expr = d[1:0] == (S_FETCH + 1);

  mod1 #(
      .WIDTH(4)
  ) cell1 (
      .q(between),
      .clk(clk),
      .d(d[3:0])
  );

  mod2 cell2 (
      .d(between),
      .q(q[3:0]),
      .clk(clk)
  );

endmodule

module mod1 #(
    parameter WIDTH = 32
) (
    input clk,
    input [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);

  localparam IGNORED = 1;

  always @(posedge clk) q <= d;

endmodule

module mod2 (
    input clk,
    input [3:0] d,
    output wire [3:0] q
);

  assign q = d;

endmodule
