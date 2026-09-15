// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module test (
    input clk
);

  import "DPI-C" context function void test_dpi();

  always @(posedge clk) begin
    test_dpi();
  end

endmodule
