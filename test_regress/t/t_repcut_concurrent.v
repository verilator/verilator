// DESCRIPTION: Verilator: Concurrent RepCut clock domains and local publication
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
module t (
    input logic clk_a, clk_b, clk_c, reset, enable,
    input logic [31:0] data,
    input logic [1:0] address,
    output logic [379:0] banks_a, banks_b,
    output logic [189:0] mixed,
    output logic [32:0] negative,
    output logic [31:0] cross_a, cross_b, left_state, right_state, predicate, guarded,
    output logic [94:0] memory_out
);
  for (genvar i = 0; i < 4; ++i) begin : banks
    logic [94:0] a, b;
    always @(posedge clk_a) begin
      if (reset) a <= 95'(i + 1);
      else if (enable) a <= {a[93:0], a[94]} ^ {31'(data + 32'(i)), data, data};
    end
    always @(posedge clk_b) begin
      if (reset) b <= 95'(i + 9);
      else if (enable) b <= {b[93:0], b[94]} ^ {31'(data - 32'(i)), data, data};
    end
    assign banks_a[95*i +: 95] = a;
    assign banks_b[95*i +: 95] = b;
  end
  // One output spans different clock domains on the same partition owner.
  // Its native union-clock guard must not be replaced by one owner's guard.
  assign mixed = {banks_b[94:0], banks_a[94:0]};
  always @(negedge clk_c) begin
    if (reset) negative <= 33'd5;
    else if (enable) negative <= negative + {1'b0, data};
  end
`ifdef ISOLATED
  assign cross_a = 0;
  assign cross_b = 0;
  assign left_state = 0;
  assign right_state = 0;
  assign predicate = 0;
  assign guarded = 0;
`else
  // Both cross-clock scalars deliberately have the same partition owner.
  always @(posedge clk_a) begin
    if (reset) begin
      cross_a <= 32'd1;
      left_state <= 32'd3;
      right_state <= 32'd7;
      predicate <= 32'd0;
      guarded <= 32'd11;
    end else begin
      cross_a <= cross_b + data;
      left_state <= right_state + data;
      right_state <= left_state ^ data;
      predicate <= data;
      if (predicate[0]) guarded <= guarded + data;
    end
  end
  always @(posedge clk_b) begin
    if (reset) cross_b <= 32'd2;
    else cross_b <= cross_a ^ data;
  end
`endif
  logic [94:0] memory [0:3];
  always @(posedge clk_b) begin
    if (reset) begin
      for (int i = 0; i < 4; ++i) memory[i] <= 95'(i);
    end else if (enable) begin
      memory[address] <= {31'(data), data, data};
      // Ordered overlapping partial writes must retain source priority.
      if (data[0]) memory[address][63:32] <= ~data;
    end
  end
  assign memory_out = memory[address];
endmodule
