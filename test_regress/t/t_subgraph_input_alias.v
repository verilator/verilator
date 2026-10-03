// DESCRIPTION: Verilator: Input aliases through internal modules remain inside the contract
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
  wire clk2;
  assign clk2 = clk;
  int unsigned cycles = 0;
  logic [6:0] d = 1;
  logic [6:0] expected = 1;
  logic [6:0] parent_q = 1;
  logic [6:0] expected_direct = 1;
  wire [6:0] direct0;
  wire [6:0] direct1;
  wire [6:0] q0;
  wire [6:0] q1;

  sg_input_alias i0 (.clk(clk2), .d(d), .q(q0), .direct_q(direct0));
  sg_input_alias i1 (.clk(clk2), .d(d), .q(q1), .direct_q(direct1));

  always_ff @(posedge clk2) begin
    `checkh(q0, expected);
    `checkh(q1, expected);
    `checkh(parent_q, expected);
    `checkh(direct0, expected_direct);
    `checkh(direct1, expected_direct);
    if (cycles == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    parent_q <= (d + 7'h13) * (d ^ 7'h35);
    expected <= (d + 7'h13) * (d ^ 7'h35);
    expected_direct <= d;
    d <= d + 7'(cycles * 3) + 7'd1;
    cycles <= cycles + 1;
  end
endmodule

module sg_input_alias (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1,
  output logic [6:0] direct_q = 1
);
  /*verilator subgraph_boundary*/
  wire clk2;
  wire [6:0] next_q;
  wire [6:0] forwarded;
  sg_input_alias_comb u_comb (.clk(clk), .d(d), .clk_out(clk2),
                             .y(next_q), .forwarded(forwarded));
  always_ff @(posedge clk2) begin
    q <= next_q;
    direct_q <= forwarded;
  end
endmodule

module sg_input_alias_comb (
  input logic clk,
  input logic [6:0] d,
  output wire clk_out,
  output wire [6:0] y,
  output wire [6:0] forwarded
);
  /*verilator no_inline_module*/
  assign clk_out = clk;
  assign y = (d + 7'h13) * (d ^ 7'h35);
  assign forwarded = d;
endmodule
