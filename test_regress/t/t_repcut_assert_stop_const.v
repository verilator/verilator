// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  int cyc = 0;
  // A constant sequence has no sampled-value node left after optimization.
  assert property (@(posedge clk) 1'b1 ##5 1'b1) $write("ACTION_RAN\n");
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) $stop;
  end
endmodule
