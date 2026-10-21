// DESCRIPTION: Verilator: Shared module scope traversal
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module leaf (
    input logic clk,
    input logic data,
    output logic result
);
  always_ff @(posedge clk) result <= data;
endmodule

module pair (
    input logic clk,
    input logic data,
    output logic result
);
  logic intermediate;
  leaf first (
      .clk,
      .data,
      .result(intermediate)
  );
  leaf second (
      .clk,
      .data(intermediate),
      .result
  );
endmodule

module t #(
    parameter int COUNT = 7
) (
    input logic clk,
    input logic [COUNT-1:0] data,
    output logic [COUNT-1:0] result
);
  for (genvar i = 0; i < COUNT; ++i) begin : instances
    pair item (
        .clk,
        .data(data[i]),
        .result(result[i])
    );
  end
endmodule
