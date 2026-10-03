// DESCRIPTION: Verilator: Shared subgraph FF without data inputs
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

  sg_shared_counter i0 (.clk(clk), .q(q0));
  sg_shared_counter i1 (.clk(clk), .q(q1));

  always @(posedge clk) begin
    `checkh(q0, 8'(cycles + 1));
    `checkh(q1, 8'(cycles + 1));
    if (cycles == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    cycles <= cycles + 1;
  end
endmodule

module sg_shared_counter (
  input logic clk,
  output logic [7:0] q = 1
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= q + 1;
endmodule
