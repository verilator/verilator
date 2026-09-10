// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  logic [6:0] c;
} nested_t;

typedef struct {
  logic [30:0] a;
  logic [6:0] b;
  nested_t nested;
} response_t;

module top;
  response_t forceable_response /* verilator forceable */;
endmodule
