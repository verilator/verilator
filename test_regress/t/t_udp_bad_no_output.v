// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

primitive t_gate(a, b);
  input a, b;

  table
    0 0 : 0;
  endtable
endprimitive

module top (a, b);
  input a, b;
  t_gate(a, b);
endmodule
