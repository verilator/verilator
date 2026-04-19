// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eunseo Song
// SPDX-License-Identifier: CC0-1.0

module top (
    input clk,
    input rst,
    output reg [7:0] count
);

  always @(posedge clk) begin
    if (rst) count <= 0;
    else count <= count + 1;
  end

  initial begin
    $display("Hello from t_flag_csplit_pch");
    $write("*-* All Coverage-Coverage = 1\n");
    $finish;
  end
endmodule
