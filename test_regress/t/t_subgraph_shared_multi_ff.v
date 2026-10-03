// DESCRIPTION: Verilator: Shared subgraph schedules several FF outputs once
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0)
// verilog_format: on

module t (
  input logic clk
);
  int unsigned cycles = 0;
  wire [6:0] a0;
  wire [6:0] b0;
  wire [6:0] a1;
  wire [6:0] b1;
  wire [6:0] c0;
  wire [6:0] c1;
  wire [6:0] d0;
  wire [6:0] d1;
  logic [6:0] expected_a0 = 1;
  logic [6:0] expected_b0 = 2;
  logic [6:0] expected_a1 = 1;
  logic [6:0] expected_b1 = 2;
  logic [6:0] expected_c0 = 3;
  logic [6:0] expected_c1 = 3;
  logic [6:0] expected_d0 = 4;
  logic [6:0] expected_d1 = 4;
  logic [6:0] parent_q = 0;
  logic [6:0] expected_parent = 0;

  sg_shared_multi_ff i0 (.clk(clk), .d(b1), .e(a1), .a(a0), .b(b0));
  sg_shared_multi_ff i1 (.clk(clk), .d(b0 + 7'd1), .e(a0 + 7'd2), .a(a1), .b(b1));
  sg_shared_split_ff j0 (.clk(clk), .en(cycles[0]), .d(b1), .e(a1), .q(c0), .r(d0));
  sg_shared_split_ff j1 (.clk(clk), .en(!cycles[0]), .d(b0), .e(a0), .q(c1), .r(d1));

  always @(posedge clk) begin
    `checkh(a0, expected_a0);
    `checkh(b0, expected_b0);
    `checkh(a1, expected_a1);
    `checkh(b1, expected_b1);
    `checkh(c0, expected_c0);
    `checkh(c1, expected_c1);
    `checkh(d0, expected_d0);
    `checkh(d1, expected_d1);
    `checkh(parent_q, expected_parent);
    if (cycles == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    expected_a0 <= expected_a0 + expected_b1;
    expected_b0 <= expected_b0 + expected_a1 + expected_a0;
    expected_a1 <= expected_a1 + expected_b0 + 7'd1;
    expected_b1 <= expected_b1 + expected_a0 + 7'd2 + expected_a1;
    if (cycles[0]) expected_c0 <= expected_c0 + expected_b1;
    if (!cycles[0]) expected_c1 <= expected_c1 + expected_b0;
    expected_d0 <= expected_d0 + expected_c0 + expected_a1;
    expected_d1 <= expected_d1 + expected_c1 + expected_a0;
    parent_q <= a0;
    expected_parent <= expected_a0;
    cycles <= cycles + 1;
  end
endmodule

module sg_shared_split_ff (
  input logic clk,
  input logic en,
  input logic [6:0] d,
  input logic [6:0] e,
  output logic [6:0] q = 3,
  output logic [6:0] r = 4
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) begin
    if (en) q <= q + d;
  end
  always_ff @(posedge clk) r <= r + q + e;
endmodule

module sg_shared_multi_ff (
  input logic clk,
  input logic [6:0] d,
  input logic [6:0] e,
  output logic [6:0] a = 1,
  output logic [6:0] b = 2
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) begin
    a <= a + d;
    b <= b + e + a;
  end
endmodule
