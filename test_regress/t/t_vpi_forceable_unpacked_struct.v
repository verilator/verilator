// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct {logic [7:0] c;} nested_t;

typedef struct {
  logic [31:0] a;
  logic [15:0] b;
  nested_t nested;
} response_t;

module top;
  response_t forceable_response  /* verilator forceable */;
endmodule
