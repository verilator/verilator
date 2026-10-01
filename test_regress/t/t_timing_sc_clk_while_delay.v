// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 ViraSemi Inc.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int edges = 0;

  always @(posedge clk) edges <= edges + 1;

  initial begin
    // Every clock edge must be seen while this delay is pending
    #995ns;
    if (edges != 100) begin
      $write("%%Error: %0d clock edges seen while a delay was pending, expected 100\n", edges);
      $stop;
    end
    // No delay is pending from here on; the clock alone must keep the model running
    wait (edges == 150);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
