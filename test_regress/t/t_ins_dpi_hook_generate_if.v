// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets around conditional generate blocks (in an if-generate block (g_en), at the top next
// to a block signal of the same name (cnt), under items without begin/end (u, nb))
module sub (
    input logic clk,
    output logic [7:0] q
);
  logic [7:0] r = 8'h10;
  always @(posedge clk) r <= r + 1;
  assign q = r;
endmodule

module top_module;
  parameter EN = 1;

  logic clk = 0;
  int cyc = 0;
  logic [7:0] q;
  logic [7:0] p;
  logic [7:0] cnt = 8'h10;
  logic [7:0] qs;
  logic [7:0] ps;
  logic [7:0] qu;
  logic [7:0] vw;

  generate
    if (EN) begin : g_en
      logic [7:0] cnt = 8'h10;
      always @(posedge clk) cnt <= cnt + 1;
      assign q = cnt;
    end
    if (!EN) begin : g_off
      logic [7:0] cnt = 8'hFF;
      assign q = cnt;
    end
  endgenerate

  generate
    if (EN) begin : g_alt
      logic [7:0] cnt = 8'h40;
      always @(posedge clk) cnt <= cnt + 1;
      assign p = cnt;
    end
  endgenerate

  always @(posedge clk) cnt <= cnt + 1;
  assign qs = cnt;

  generate
    if (1) begin : g_sh
      logic [7:0] cnt = 8'h40;
      always @(posedge clk) cnt <= cnt + 1;
      assign ps = cnt;
    end
  endgenerate

  if (EN)
    sub u (
        .clk(clk),
        .q(qu)
    );
  if (EN)
    if (EN) begin : nb
      logic [7:0] w = 8'h50;
      always @(posedge clk) w <= w + 1;
      assign vw = w;
    end

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("$[%0d| q: %02x p: %02x]", cyc, q, p);
    $display("sh $[%0d| q: %02x p: %02x]", cyc, qs, ps);
    $display("$[%0d| q: %02x v: %02x]", cyc, qu, vw);
    if (cyc > 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
