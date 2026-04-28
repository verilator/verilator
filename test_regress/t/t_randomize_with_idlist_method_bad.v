// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  int q[$];
  int total;
  initial begin
    q.push_back(1);
    q.push_back(2);
    total = q.sum() with (item) { item > 0; };
  end
endmodule
