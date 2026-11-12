// DESCRIPTION: Verilator: nested interface array port connections
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Verilator contributors
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface inner_if #(parameter int W = 8);
  logic [W-1:0] data;
  logic [W-1:0] response;
endinterface

interface outer_if #(parameter int W = 7);
  inner_if #(W) inner[2]();
endinterface

module reader #(parameter int W = 8, parameter bit DRIVE = 1)(
    inner_if p, output logic [W-1:0] y
);
  assign y = p.data;
  if (DRIVE) assign p.response = ~p.data;
  initial `checkh($bits(p.data), W);
endmodule

module t;
  outer_if left();
  outer_if #(13) right();
  outer_if #(7) explicit_default();
  wire [6:0] l[2];
  wire [12:0] r[2];

  for (genvar i = 0; i < 2; ++i) begin : g
    reader #(7) a(.p(left.inner[i]), .y(l[i]));
    reader #(13) b(.p(right.inner[i]), .y(r[i]));
  end
  wire [12:0] constant_result;
  reader #(13, 0) c(.p(right.inner[1]), .y(constant_result));
  wire [6:0] default_result;
  reader #(7) d(.p(explicit_default.inner[1]), .y(default_result));

  initial begin
    for (int cycle = 0; cycle < 4; ++cycle) begin
      left.inner[0].data = 7'h12 ^ 7'(cycle);
      left.inner[1].data = 7'h34 ^ 7'(cycle);
      right.inner[0].data = 13'h567 ^ 13'(cycle);
      right.inner[1].data = 13'h189a ^ 13'(cycle);
      explicit_default.inner[1].data = 7'h25 ^ 7'(cycle);
      #1;
      `checkh(l[0], 7'h12 ^ 7'(cycle));
      `checkh(l[1], 7'h34 ^ 7'(cycle));
      `checkh(r[0], 13'h567 ^ 13'(cycle));
      `checkh(r[1], 13'h189a ^ 13'(cycle));
      `checkh(constant_result, 13'h189a ^ 13'(cycle));
      `checkh(left.inner[0].response, 7'h6d ^ 7'(cycle));
      `checkh(left.inner[1].response, 7'h4b ^ 7'(cycle));
      `checkh(right.inner[0].response, 13'h1a98 ^ 13'(cycle));
      `checkh(right.inner[1].response, 13'h765 ^ 13'(cycle));
      `checkh(default_result, 7'h25 ^ 7'(cycle));
      `checkh(explicit_default.inner[1].response, 7'h5a ^ 7'(cycle));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
