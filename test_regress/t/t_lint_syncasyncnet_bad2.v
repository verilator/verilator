// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
  input clk_i,
  input rst_ni,
  output reg out
);
/* verilator no_inline_module */
// no-inline to root module
  logic lfsr_d;
  always_ff @(negedge rst_ni) begin
    if (!rst_ni) begin
      lfsr_d <= lfsr_d;
    end
  end
  NextStateCheck: assert property (@(posedge clk_i) rst_ni);
  always_ff @(posedge clk_i) begin
    out <= (rst_ni) ? 0 : 1;
  end
endmodule
