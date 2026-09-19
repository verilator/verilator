// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  int x;
  logic a;

  default clocking cb @(posedge clk); endclocking

  assert property (always [-1:3] a);
  assert property (always [5:2] a);
  assert property (always [x:3] a);
  assert property (always [1:x] a);
  assert property (s_always a);
  assert property (s_always [1:$] a);

  localparam int unsigned MAX = 32'h7fffffff;
  localparam int unsigned MAX_M1 = 32'h7ffffffe;
  localparam int unsigned MAX_M3 = 32'h7ffffffc;
  assert property (always [0:MAX] a);
  assert property (always [MAX_M1:$] a);
  assert property (s_always [0:MAX_M3] a);

endmodule
