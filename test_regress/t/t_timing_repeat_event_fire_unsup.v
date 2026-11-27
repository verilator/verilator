// DESCRIPTION: Verilator: event. This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Xia Chao. SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  event ev;

  always #1 clk = ~clk;

  initial begin
    ->> repeat (2) @(posedge clk) ev;
  end
endmodule
