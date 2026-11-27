// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int u[2][2];
  int w[2][*];
  bit r;

  initial begin
    r = 1 inside {u};
    r = 1 inside {w};
  end
endmodule
