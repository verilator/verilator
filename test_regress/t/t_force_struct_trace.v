// DESCRIPTION: Verilator: Verilog Test module
//
// Minimal reproducer for Verilator 5.048 internal error:
//   V3Force.cpp:216: `force` assignment has no VarRef on LHS
//
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zubin Jain
// SPDX-License-Identifier: CC0-1.0

module t;
  logic forced_sig;
  typedef struct {
    logic [1:0] d[0:1];
  } payload_t;
  payload_t s;
  initial begin
    force forced_sig = 1'b1;
    $finish(0);
  end
endmodule
