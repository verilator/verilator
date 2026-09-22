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

module t;
  response_t forceable_response  /* verilator forceable */;

  bit run_mon_check;
  initial begin
    run_mon_check = 1'b1;
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
