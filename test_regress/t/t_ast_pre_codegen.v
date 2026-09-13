// DESCRIPTION: Verilator: JSON output after optional sampled lowering
//
// This file ONLY is placed under the Creative Commons Public Domain, for any use,
// without warranty, 2026 by Verilator Authors. SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [7:0] data,
    input logic [2:0] index,
    output logic [7:0] entry,
    output logic [7:0] value
);
  logic [7:0] mem[8];
  assign entry = mem[index];

  always @(posedge clk) begin
`ifdef WITH_SAMPLED
    value <= $sampled(data);
    mem[index] <= $sampled(data);
`else
    value <= data;
    mem[index] <= data;
`endif
  end
endmodule
