// DESCRIPTION: Verilator: Instances in a mesh share code through kept array-of-struct ports
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  logic v;
  logic [15:0] data;
} link_s;

module tile (
    input logic clk,
    input logic [15:0] seed_i,
    input link_s [3:0] link_i,
    output link_s [3:0] link_o,
    output logic [15:0] acc_o
);
  /*verilator no_inline_module*/
  logic [15:0] acc = 0;
  always_ff @(posedge clk) begin
    acc <= acc + seed_i + (link_i[0].v ? link_i[0].data : 16'h0)
        + (link_i[1].v ? link_i[1].data : 16'h0) + (link_i[2].v ? link_i[2].data : 16'h0)
        + (link_i[3].v ? link_i[3].data : 16'h0);
  end
  for (genvar d = 0; d < 4; ++d) begin : g_out
    assign link_o[d] = '{v: acc[d], data: acc ^ link_i[3-d].data};
  end
  assign acc_o = acc;
endmodule

module t;
  localparam int N = 2;
  logic clk = 0;
  link_s [3:0] lo[N][N];
  link_s [3:0] li[N][N];
  logic [15:0] acc[N][N];
  // The links at the edges are tied off, the others come from neighbors
  for (genvar y = 0; y < N; ++y) begin : g_y
    for (genvar x = 0; x < N; ++x) begin : g_x
      assign li[y][x][0] = (x > 0) ? lo[y][x-1][1] : '0;
      assign li[y][x][1] = (x < N - 1) ? lo[y][x+1][0] : '0;
      assign li[y][x][2] = (y > 0) ? lo[y-1][x][3] : '0;
      assign li[y][x][3] = (y < N - 1) ? lo[y+1][x][2] : '0;
      tile u (
          .clk,
          .seed_i(16'(y * N + x + 1)),
          .link_i(li[y][x]),
          .link_o(lo[y][x]),
          .acc_o(acc[y][x])
      );
    end
  end

  always #1 clk = ~clk;

  initial begin
    logic [15:0] sum;
    repeat (40) @(posedge clk);
    #0.5;
    sum = 0;
    for (int y = 0; y < N; ++y) for (int x = 0; x < N; ++x) sum = sum ^ acc[y][x];
    `checkh(sum, 16'h1dd5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
