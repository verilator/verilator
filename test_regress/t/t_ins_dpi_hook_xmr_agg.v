// DESCRIPTION: Verilator: DPI-hook targets inside aggregates, read by the parent through
// hierarchical references
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic [3:0] a;
  logic [7:0] b;
} pst_t;

typedef struct {
  logic [7:0] x;
  logic [7:0] y;
} pair_t;

module sub (
    input logic clk,
    input int cyc
);
  logic [7:0] mem[4];
  pst_t s;
  pair_t p;

  initial for (int i = 0; i < 4; i++) mem[i] = 0;

  always @(posedge clk) begin
    mem[cyc[1:0]] <= 8'h40 + cyc[7:0];
    s <= {cyc[3:0], 8'h80 + cyc[7:0]};
    p.x <= 8'h10 + cyc[7:0];
    p.y <= 8'h20 + cyc[7:0];
  end
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] o_mem1, o_mem2, o_sb, o_px, o_py;
  logic [3:0] o_sa;

  sub u (
      .clk(clk),
      .cyc(cyc)
  );

  assign o_mem1 = u.mem[1];
  assign o_mem2 = u.mem[2];
  assign o_sb = u.s.b;
  assign o_sa = u.s.a;
  assign o_px = u.p.x;
  assign o_py = u.p.y;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] mem1=%02x mem2=%02x sb=%02x sa=%x px=%02x py=%02x", cyc, o_mem1, o_mem2, o_sb,
             o_sa, o_px, o_py);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
