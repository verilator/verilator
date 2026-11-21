// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets read in a sensitivity list, as a clock or in an event control without an edge, also
// in another module through a hierarchical reference or an interface port
module top_module;
  typedef struct {
    logic       c;
    logic [7:0] d;
  } clkd_t;

  reg clk = 0;
  reg [7:0] in1 = 8'h11;
  reg [7:0] in2 = 8'h22;
  logic [7:0] out, outq;
  clkd_t cs;
  logic ck2[2];
  struct packed {
    logic       c;
    logic [6:0] b;
  } pk;
  logic [7:0] acc = 0;
  logic [7:0] acc2 = 0;
  logic [7:0] acc3 = 0;
  logic [7:0] n;
  clk_if ci ();

  module_a a1 (
      .clk(clk),
      .in1(in1),
      .in2(in2),
      .out(out),
      .outq(outq)
  );

  always @(posedge cs.c) acc <= acc + cs.d;
  always @(posedge ck2[0] or posedge pk.c) acc2 <= acc2 + 8'(pk.b);

  ticker tk (.clk(clk));
  always @(posedge tk.tick) acc3 <= acc3 + 8'd1;
  assign ci.c = clk;
  ifc_user iu (
      .b(ci),
      .n(n)
  );

  initial begin
    repeat (4) #1 clk = ~clk;
    $display("%x %x %x %x", out, outq, acc, acc2);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule

module module_a (
    input logic clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out,
    output logic [7:0] outq
);
  logic [7:0] sum;
  assign sum = in1 + in2;
  always @(sum or in2) out = sum ^ in2;
  always_ff @(posedge clk) outq <= in1;
endmodule

module ticker (
    input logic clk
);
  logic tick = 1'b0;
  always_ff @(posedge clk) tick <= ~tick;
endmodule

interface clk_if;
  logic c;
endinterface

module ifc_user (
    clk_if b,
    output logic [7:0] n
);
  always_ff @(posedge b.c) n <= n + 8'd1;
endmodule
