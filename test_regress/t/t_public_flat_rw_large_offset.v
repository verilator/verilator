// DESCRIPTION: Verilator: Test public variable offsets larger than 32 bits
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  longint padding1[1<<28];
  longint padding2[1<<28];
  longint padding3[1<<28];
endmodule
