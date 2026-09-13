// DESCRIPTION: Verilator: JSON output after optional sampled lowering
//
// This file ONLY is placed under the Creative Commons Public Domain, for any use,
// without warranty, 2026 by Verilator Authors. SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [7:0] data,
    output logic [7:0] value
);
  always @(posedge clk) begin
`ifdef WITH_SAMPLED
    value <= $sampled(data);
`else
    value <= data;
`endif
  end
endmodule
