// DESCRIPTION: Verilator: Expression coverage in sensitivity expressions
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk;
  bit gate = 1;
  int event_count;

  always @(posedge (clk && gate)) begin  // COVER_SENSITIVITY_EXPR
    event_count++;
    if (event_count == -1) $finish;
  end

  initial begin
    #1 clk = 1;
    #1;
    if (event_count != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
