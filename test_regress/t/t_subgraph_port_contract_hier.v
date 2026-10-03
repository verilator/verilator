// DESCRIPTION: Verilator: Hierarchical child-state access falls back from port-only scheduling
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
  logic [7:0] observed = 0;
  logic [7:0] observed1 = 0;

  sg_port_contract_hier i0 (.clk(clk), .q(q0));
  sg_port_contract_hier i1 (.clk(clk), .q(q1));

  always @(posedge clk) begin
    if (cycles > 0) begin
      `checkh(observed, q0);
      `checkh(observed1, q1);
      `checkh(q0, q1);
    end
    if (cycles == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    observed <= i0.state;
    observed1 <= i1.state;
    cycles <= cycles + 1;
  end
endmodule

module sg_port_contract_hier (input logic clk, output logic [7:0] q = 1);
  /*verilator subgraph_boundary*/
  logic [7:0] state = 3;
  always_ff @(posedge clk) begin
    state <= state + 1;
    q <= state;
  end
endmodule
