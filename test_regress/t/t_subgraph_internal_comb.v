// DESCRIPTION: Verilator: Schedule internal combinational next-state logic in shared subgraphs
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
  wire [7:0] q0;
  wire [7:0] q1;
  logic [7:0] expected0 = 1;
  logic [7:0] expected1 = 1;

`ifdef SUBGRAPH_WRAPPER
  sg_internal_comb_wrapper i0 (.clk(clk), .d(q1), .q(q0));
  sg_internal_comb_wrapper i1 (.clk(clk), .d(q0 + 8'd3), .q(q1));
`else
  sg_internal_comb i0 (.clk(clk), .d(q1), .q(q0));
  sg_internal_comb i1 (.clk(clk), .d(q0 + 8'd3), .q(q1));
`endif

  always @(posedge clk) begin
    `checkh(q0, expected0);
    `checkh(q1, expected1);
    if (cycles == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    expected0 <= expected0 + expected1 + (expected1[0] ? 8'd1 : 8'd2);
    expected1 <= expected1 + expected0 + 8'd3
                 + (((expected0 + 8'd3) & 8'd1) != 0 ? 8'd1 : 8'd2);
    cycles <= cycles + 1;
  end
endmodule

module sg_internal_comb (
  input logic clk,
  input logic [7:0] d,
  output logic [7:0] q = 1
);
  /*verilator subgraph_boundary*/
  logic [7:0] intermediate;
  logic [7:0] next_q;
  function automatic logic [7:0] advance(input logic [8:0] sig_a, input logic [7:0] sig_b);
    // verilator no_inline_task
    return sig_a[7:0] + sig_b;
  endfunction
  always_comb begin
    intermediate = q + d;
    if (d[0]) next_q = advance({1'b0, intermediate}, 8'd1);
    else next_q = advance({1'b0, intermediate}, 8'd2);
  end
  always_ff @(posedge clk) q <= next_q;
endmodule

`ifdef SUBGRAPH_WRAPPER
module sg_internal_comb_wrapper (
  input logic clk,
  input logic [7:0] d,
  output logic [7:0] q
);
  sg_internal_comb i_child (.clk(clk), .d(d), .q(q));
endmodule
`endif
