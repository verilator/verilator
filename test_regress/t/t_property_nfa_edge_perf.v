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
    input a
);
  assert property (@(posedge clk) `S4);
endmodule
