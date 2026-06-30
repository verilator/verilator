// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2016 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  // verilator lint_off REALCVT
  // verilator lint_off SHORTREAL
  shortreal s;
  logic l;

  initial l = s[0];

endmodule
