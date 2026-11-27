// DESCRIPTION: Verilator: Clocked RepCut DPI boundary regression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input bit clk,
  input bit reset,
  input bit enable,
  input int unsigned x,
  output int unsigned q,
  output int unsigned old_q,
  output logic [94:0] wide_q,
  output int unsigned rtl_q
);
  import "DPI-C" function int unsigned repcut_tick(
    input string tag, input int unsigned x,
    output int unsigned y, inout int unsigned z);
  import "DPI-C" function void repcut_wide(
    input logic [94:0] x, output logic [94:0] y);
  int unsigned y, z, r;
  logic [94:0] wide;
  wire [31:0] argument = x ^ rtl_q;

  always @(posedge clk) begin
    if (reset) begin
      y = 0;
      z = 1;
      r = 0;
      wide = 0;
      q <= 0;
      old_q <= 0;
      wide_q <= 0;
    end else if (enable) begin
      $display("ORDER before %0x", q);
      r = repcut_tick("first", argument + q, y, z);
      if (r[0]) r = repcut_tick("second", y ^ r, y, z);
      repcut_wide({31'(r), y, z}, wide);
      q <= y + z + r;
      old_q <= q;
      wide_q <= wide;
      $display("ORDER after %0x", r);
    end
  end
  always @(posedge clk) begin
    if (reset) rtl_q <= 0;
    else rtl_q <= x + q;
  end
endmodule
