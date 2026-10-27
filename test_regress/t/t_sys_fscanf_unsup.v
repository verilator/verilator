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

  always @($fscanf(f, "%h", d1[3:0])) d1 = d1 + 1;  // UNSUPPORTED
  always @($sscanf(s, "%h", d2[3:0])) d2 = d2 + 1;  // UNSUPPORTED
  always @($fscanf(f, "%h", d1)) d1 = d1 + 1;  // Legal: addressable destination
  always @($sscanf(s, "%h", d2)) d2 = d2 + 1;  // Legal: addressable destination
endmodule
