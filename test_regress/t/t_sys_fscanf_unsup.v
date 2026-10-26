// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  integer f;
  integer d1;
  integer d2;
  string s;

  always @($fscanf(f, "%d", d1)) d1 = d1 + 1;  // UNSUPPORTED
  always @($sscanf(s, "%d", d2)) d2 = d2 + 1;  // UNSUPPORTED
endmodule
