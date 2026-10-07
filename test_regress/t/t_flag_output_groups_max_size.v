// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t #(
    // Enough independent statements to generate several MB of C++
    parameter int N = 12000
) (
    input clk
);
  logic [63:0] r[N];
  logic [63:0] sum;
  int cyc = 0;

  for (genvar i = 0; i < N; ++i) begin : g_reg
    always_ff @(posedge clk) r[i] <= r[(i*7+1)%N] ^ (r[(i*13+5)%N] + 64'(i));
  end

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      sum = '0;
      for (int i = 0; i < N; ++i) sum ^= r[i];
      $display("sum=%x", sum);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
