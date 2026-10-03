// DESCRIPTION: Verilator: Schedule feedthrough port connections inside a subgraph
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

  sg_internal_ports i0 (.clk(clk), .d(q1), .q(q0));
  sg_internal_ports i1 (.clk(clk), .d(q0 + 7'd3), .q(q1));

  always @(posedge clk) begin
    `checkh(q0, expected0);
    `checkh(q1, expected1);
    if (cycles == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    expected0 <= expected0 + expected1 + 7'd1;
    expected1 <= expected1 + expected0 + 7'd4;
    cycles <= cycles + 1;
  end
endmodule

module sg_internal_ports (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1
);
  /*verilator subgraph_boundary*/
  wire [6:0] next_q;
  sg_internal_ports_comb u_comb (.a(q), .b(d), .y(next_q));
  always_ff @(posedge clk) q <= next_q;
endmodule

// Public inputs keep the port assignments from being optimized away.
module sg_internal_ports_comb (
  input logic [6:0] a /*verilator public_flat*/,
  input logic [6:0] b /*verilator public_flat*/,
  output wire [6:0] y
);
  /*verilator no_inline_module*/
  wire [6:0] sum;
  sg_internal_ports_leaf u_leaf (.a(a), .b(b), .y(sum));
  assign y = sum + 7'd1;
endmodule

module sg_internal_ports_leaf (
  input logic [6:0] a /*verilator public_flat*/,
  input logic [6:0] b /*verilator public_flat*/,
  output wire [6:0] y
);
  /*verilator no_inline_module*/
  assign y = a + b;
endmodule
