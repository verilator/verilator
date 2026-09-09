// DESCRIPTION: Verilator: DPI-hooks on aggregates read as a whole (copies, function
// arguments, neighbour members, hierarchical references)
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
    input int cyc,
    output logic [7:0] o_mem2,
    output logic [7:0] o_sum,
    output logic [11:0] o_s,
    output logic [3:0] o_sa,
    output logic [15:0] o_p,
    output logic [15:0] o_p2,
    output logic [7:0] o_w0,
    output logic [7:0] o_w1
);
  logic [7:0] mem[4];
  pst_t s;
  pair_t p;
  logic [7:0] w[2];
  logic [7:0] mem2[4];
  pair_t p2;
  logic [7:0] w2[2];

  function automatic logic [7:0] sum4(input logic [7:0] v[4]);
    return v[0] + v[1] + v[2] + v[3];
  endfunction

  function automatic logic [15:0] pk(input pair_t v);
    return {v.x, v.y};
  endfunction

  initial for (int i = 0; i < 4; i++) mem[i] = 0;

  always @(posedge clk) begin
    mem[cyc[1:0]] <= 8'h40 + cyc[7:0];
    s <= {cyc[3:0], 8'h80 + cyc[7:0]};
    p.x <= 8'h10 + cyc[7:0];
    p.y <= 8'h20 + cyc[7:0];
    w[cyc[0]] <= 8'h30 + cyc[7:0];
  end

  assign mem2 = mem;
  assign p2 = p;
  assign w2 = w;

  assign o_mem2 = mem2[1];
  assign o_sum = sum4(mem);
  assign o_s = s;
  assign o_sa = s.a;
  assign o_p = pk(p);
  assign o_p2 = {p2.x, p2.y};
  assign o_w0 = w2[0];
  assign o_w1 = w2[1];
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] o_mem2, o_sum, o_w0, o_w1;
  logic [11:0] o_s, o_xs;
  logic [3:0] o_sa;
  logic [15:0] o_p, o_p2;

  sub u (
      .clk(clk),
      .cyc(cyc),
      .o_mem2(o_mem2),
      .o_sum(o_sum),
      .o_s(o_s),
      .o_sa(o_sa),
      .o_p(o_p),
      .o_p2(o_p2),
      .o_w0(o_w0),
      .o_w1(o_w1)
  );

  assign o_xs = u.s;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] mem2=%02x sum=%02x s=%03x sa=%x xs=%03x p=%04x p2=%04x w=%02x %02x", cyc,
             o_mem2, o_sum, o_s, o_sa, o_xs, o_p, o_p2, o_w0, o_w1);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
