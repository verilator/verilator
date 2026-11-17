// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef struct {
    struct {logic [7:0] value;} arr[2];
    logic [7:0] mem[2];
    logic flag;
  } st_t;
  st_t s;
  st_t so;  // Only so.mem is forced
  int i;
  logic [7:0] q;
  logic [7:0] qo;
  assign q = s.arr[i].value;
  assign qo = so.arr[i].value;

  initial begin
    force s.arr[1].value = 8'ha5;
    force so.mem[1] = 8'h30;
    $finish;
  end
endmodule
