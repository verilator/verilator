// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t #(
    parameter NUM_LANES = 1
);

  reg [(NUM_LANES*8)-1:0] link_data_reg, link_data_reg_in;
  reg [1:0] other;
  always @(*) begin
    if (NUM_LANES >= 2) begin  // Not a generate if
      link_data_reg_in = {{((NUM_LANES - 2) * 8) {1'b0}}, link_data_reg[15:8]};
    end
    other = {32'bz{1'b1}};
  end

  wire ok1 = 1'b1;
  wire [6:0] ok7 = {3'b111{ok1}};  // Ok
endmodule
