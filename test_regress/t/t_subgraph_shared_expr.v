// DESCRIPTION: Verilator: Shared subgraph captures several inputs for a next-state expression
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

  sg_shared_expr i0 (.clk(clk), .d(7'(cycles)), .e(7'(cycles + 5)), .q(q0));
  sg_shared_expr i1 (.clk(clk), .d(7'(cycles + 9)), .e(7'(cycles + 13)), .q(q1));

  always @(posedge clk) begin
    if (cycles == 0) begin
      `checkh(q0, 7'd1);
      `checkh(q1, 7'd1);
    end else begin
      `checkh(q0, (7'(cycles - 1) ^ 7'(cycles + 4)) + 7'd3);
      `checkh(q1, (7'(cycles + 8) ^ 7'(cycles + 12)) + 7'd3);
    end
    if (cycles == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    cycles <= cycles + 1;
  end
endmodule

module sg_shared_expr (
  input logic clk,
  input logic [6:0] d,
  input logic [6:0] e,
  output logic [6:0] q = 1
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= (d ^ e) + 7'd3;
endmodule
