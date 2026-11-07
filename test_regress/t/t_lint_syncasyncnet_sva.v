// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input rst,
    input a,
    input b,
    output reg o
);
  always_ff @(posedge clk or negedge rst) begin
    o <= ~rst;
  end
  assert property (@(posedge clk) disable iff ((rst) !== '0) ($c(1'b1)));
  assert property (@(posedge clk) (rst !== 0) ##1 (a == b));
  always @(posedge clk) assert (rst | !rst);
endmodule
