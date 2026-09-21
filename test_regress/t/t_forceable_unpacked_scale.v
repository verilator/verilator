// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic go
);
  parameter int ArraySize = 512;

  logic [7:0] mem[0:ArraySize-1]  /*verilator forceable*/;

  always @(posedge go) force mem = mem;
endmodule
