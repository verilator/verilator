// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input rst,
    input rst2,
    input a,
    input b,
    input d,
    output reg o1,
    output reg o2,
    output reg o3
);
  always_ff @(posedge clk or negedge rst) begin
    o1 <= ~rst;
  end
  // disable iff
  assert property (@(posedge clk) disable iff ((rst) !== '0) a);

  // Immediate assertion
  always @(posedge clk) assert (rst | !rst);

  // Multi-cycle assertions
  assert property (@(posedge clk) (rst !== 0) ##1 (a == b));
  assert property (@(posedge clk) disable iff (rst) a [*2] ##1 (b || rst));
  assert property (@(posedge clk) rst throughout (b ##2 a));
  assert property (@(posedge clk) a |-> ##[1:3] (b && rst));

  always_ff @(posedge clk or negedge rst2) begin
    o2 <= (~rst2) ? 1'b0 : d;
  end
  // verilog_format: off
  // Sync usage on assert's fileline should not suppress real sync usage on
  // the same line
  assert property(@(posedge clk) rst2); always_ff @(posedge clk) o3 <= rst2 ? d : 1'b0;
  // verilog_format: on
endmodule
