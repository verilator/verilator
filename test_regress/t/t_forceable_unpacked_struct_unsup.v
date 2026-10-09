// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  logic [31:0] a;
  logic [31:0] b;
} response_t;

module array_struct_top;
  response_t response[2]  /*verilator forceable*/;
endmodule
