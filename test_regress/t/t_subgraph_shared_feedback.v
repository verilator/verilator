// DESCRIPTION: Verilator: Shared subgraph feedback reads old child and parent state
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
  wire [6:0] q0;
  wire [6:0] q1;
  logic [6:0] expected0 = 1;
  logic [6:0] expected1 = 1;
  logic [6:0] parent_q = 0;
  logic [6:0] expected_parent = 0;

  sg_shared_feedback i0 (.clk(clk), .d(q1), .q(q0));
  sg_shared_feedback i1 (.clk(clk), .d(q0 + 7'd1), .q(q1));

  always @(posedge clk) begin
    `checkh(q0, expected0);
    `checkh(q1, expected1);
    `checkh(parent_q, expected_parent);
    if (cycles == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    expected0 <= expected0 + expected1;
    expected1 <= expected1 + expected0 + 7'd1;
    parent_q <= q0;
    expected_parent <= expected0;
    cycles <= cycles + 1;
  end
endmodule

module sg_shared_feedback (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= q + d;
endmodule
