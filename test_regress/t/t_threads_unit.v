// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tile (
    input clk,
    input [7:0] id,
    input [7:0] in,
    output [7:0] out,
    output [7:0] st
);
  reg [7:0] r = 0;
  // The output depends on this tile's state, the next state on the previous tile's output
  assign out = r ^ id;
  assign st = r;
  always @(posedge clk) r <= r + in + 8'd1;
endmodule

module t (
    input clk
);
  integer cyc = 0;
  wire [7:0] out[4];
  wire [7:0] st[4];
  for (genvar i = 0; i < 4; ++i) begin : g
    tile u (
        .clk(clk),
        .id(8'(i * 17)),
        .in(out[(i+3)%4]),
        .out(out[i]),
        .st(st[i])
    );
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 20) begin
      $display("%0d %0d %0d %0d", st[0], st[1], st[2], st[3]);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
