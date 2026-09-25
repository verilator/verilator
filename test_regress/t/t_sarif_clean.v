// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic a,
  input logic b,
  input logic sel,
  output logic c);

  assign c = sel ? a : b;

endmodule
