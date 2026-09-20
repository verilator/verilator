// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic i,
  output logic o
  );

  // A one long cycle
  logic a;
  assign a = a;

  // A two long cycle
  logic b, c;
  assign b = c;
  assign c = b;

  // A three long cycle, with a chain leading into it that must be left alone
  logic d, e, f;
  logic g, h;
  assign d = e;
  assign e = f;
  assign f = d;
  assign g = d;
  assign h = g;

  assign o = i ^ a ^ b ^ c ^ d ^ e ^ f ^ g ^ h;

endmodule
