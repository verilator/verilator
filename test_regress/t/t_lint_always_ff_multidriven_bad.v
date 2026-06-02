// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zhi QU
// SPDX-License-Identifier: CC0-1.0

module t(input wire clk);

  logic a;

  initial a = 1'b0;

  always_ff @(posedge a) begin
    a <= 1'b1;  // <--- Warning (suppressed with --ignore-initial-multidriven)
  end

  logic b;

  always_ff @(posedge b) begin
    b <= 1'b1;
  end

  initial b = 1'b0;  // <--- Warning (suppressed with --ignore-initial-multidriven)

  reg [1:0][1:0] q;

  always_ff @(posedge clk) begin
    for (int i = 0 ; i < 2 ; ++i)
      q[i][0] <= a; // <--- Warning
  end

  always_ff @(posedge clk) begin
    for (int i = 0 ; i < 2 ; ++i)
      q[i][1] <= a; // <--- Warning
  end

  /* verilator lint_off MULTIDRIVEN */
  reg [1:0][1:0] q2;
  /* verilator lint_on MULTIDRIVEN */

  always_ff @(posedge clk) begin
    for (int i = 0 ; i < 2 ; ++i)
      q2[i][0] <= a; // <--- NO Warning
  end

  always_ff @(posedge clk) begin
    for (int i = 0 ; i < 2 ; ++i)
      q2[i][1] <= a; // <--- NO Warning
  end

endmodule
