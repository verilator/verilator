// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define S0 a
`define S1 (`S0 ##2 `S0)
`define S2 (`S1 ##2 `S1)
`define S3 (`S2 ##2 `S2)
`define S4 (`S3 ##2 `S3)

module t (
    input clk,
    input a,
    input req,
    input [2:0] op,
    input ack
);
  assert property (@(posedge clk) `S4);
  // Each opcode is acknowledged after its own latency
  assert property (@(posedge clk) req |-> (op == 3'd0) ##1 ack or (op == 3'd1) ##2 ack
      or (op == 3'd2) ##[1:2] ack or (op == 3'd3) ##[2:4] ack or (op == 3'd4) ##1 ack [*2]
      or (op == 3'd5) ##1 !ack ##1 ack or (op == 3'd6) ##[1:3] ack or (op == 3'd7) ##4 ack);
endmodule
