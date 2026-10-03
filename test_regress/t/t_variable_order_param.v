// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [7:0] i,
    output logic [31:0] o[4]
);
  localparam logic [31:0] TAB[16] = '{
      32'h11,
      32'h22,
      32'h33,
      32'h44,
      32'h55,
      32'h66,
      32'h77,
      32'h88,
      32'h99,
      32'haa,
      32'hbb,
      32'hcc,
      32'hdd,
      32'hee,
      32'hff,
      32'h1f
  };
  logic [31:0] r[8];
  logic [7:0] s = 0;
  always_ff @(posedge clk) s <= s + i;
  for (genvar k = 0; k < 8; ++k) begin : g
    always_ff @(posedge clk) r[k] <= (r[k] + TAB[r[k][3:0]^k[3:0]]) ^ 32'(k + 1);
  end
  for (genvar k = 0; k < 4; ++k) begin : go
    assign o[k] = r[k] ^ r[k+4] ^ {24'd0, s};
  end
endmodule
