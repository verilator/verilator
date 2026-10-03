// DESCRIPTION: Verilator: Subgraph boundary identities across compiler stages
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
  wire [6:0] a;
  wire [6:0] b;
  wire [14:0] c;

  sg_lifecycle #(.W(7)) i_a (.clk(clk), .d(7'(cycles)), .q(a), .unused());
  sg_lifecycle #(.W(7)) i_b (.clk(clk), .d(7'd42), .q(b), .unused());
  sg_lifecycle #(.W(15)) i_c (.clk(clk), .d(15'(cycles + 100)), .q(c), .unused());

  always @(posedge clk) begin
    if (cycles == 0) begin
      `checkh(a, 1);
      `checkh(b, 1);
      `checkh(c, 1);
    end else begin
      `checkh(a, 7'(cycles - 1));
      `checkh(b, 42);
      `checkh(c, 15'(cycles + 99));
    end
    cycles <= cycles + 1;
    if (cycles == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module sg_lifecycle #(parameter W = 7) (
  input clk,
  input [W-1:0] d,
  output logic [W-1:0] q = 1,
  output [W-1:0] unused
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
  assign unused = q;
endmodule
