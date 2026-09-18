// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Write-only retention for RAM/regs; per-element continuous assigns reconstruct.
module t (
  input logic       clk,
  input logic       we,
  input logic [3:0] addr,
  input logic [7:0] wdata
);

  logic [7:0] mem [0:15];
  logic [7:0] last_wdata;
  logic [3:0] last_addr;

  always_ff @(posedge clk) begin
    if (we) mem[addr] <= wdata;
    last_wdata <= wdata;
    last_addr  <= addr;
  end

  // Comb unpacked arrays built one element per continuous assign, read back through a
  // variable index
  localparam int LVL0 = 8;
  localparam int LVL1 = 4;

  logic [7:0] lvl0 [0:LVL0-1];
  logic [7:0] lvl1 [0:LVL1-1];
  logic [7:0] lvl2 [0:1];
  logic [7:0] picked;

  for (genvar i = 0; i < LVL0; ++i) begin : g0
    assign lvl0[i] = wdata ^ (8'h13 * 8'(i)) ^ {4'b0, addr};
  end
  for (genvar i = 0; i < LVL1; ++i) begin : g1
    assign lvl1[i] = lvl0[2 * i] | lvl0[(2 * i) + 1];
  end
  for (genvar i = 0; i < 2; ++i) begin : g2
    assign lvl2[i] = lvl1[2 * i] & lvl1[(2 * i) + 1];
  end

  assign picked = lvl2[addr[0]];

endmodule
