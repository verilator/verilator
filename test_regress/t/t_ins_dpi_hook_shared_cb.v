// DESCRIPTION: Verilator: Targets of one width but different declared types sharing a callback
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic [3:0] hi;
  logic [3:0] lo;
} nib_t;

typedef enum logic [7:0] {
  E0 = 8'h00,
  E1 = 8'h11
} e8_t;

typedef enum int {
  I0 = 0,
  I1 = 1
} ei_t;

module holder #(
    parameter type T = logic [7:0],
    parameter int BASE = 0
) (
    input logic clk,
    input int cyc,
    output T q
);
  T t;
  always @(posedge clk) t <= T'(BASE + cyc);
  assign q = t;
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] v;
  nib_t s;
  e8_t e;
  int i;
  ei_t ie;

  holder #(.T(logic [7:0]), .BASE('h20)) u_v (.clk(clk), .cyc(cyc), .q(v));  // cb_8
  holder #(.T(nib_t), .BASE('h40)) u_s (.clk(clk), .cyc(cyc), .q(s));  // cb_8
  holder #(.T(e8_t), .BASE('h60)) u_e (.clk(clk), .cyc(cyc), .q(e));  // cb_8
  holder #(.T(int), .BASE('h100)) u_i (.clk(clk), .cyc(cyc), .q(i));  // cb_int
  holder #(.T(ei_t), .BASE('h200)) u_ie (.clk(clk), .cyc(cyc), .q(ie));  // cb_int

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] v=%02x s=%02x e=%02x i=%0x ie=%0x", cyc, v, s, e, i, ie);
    if (cyc > 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
