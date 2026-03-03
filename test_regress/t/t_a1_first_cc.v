// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  // Test loop
  always @(posedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
