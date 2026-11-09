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

// 'module' written where 'primitive' was intended
module t_mod (o, a);
  output o;
  input a;

  table
    0 : 0;
  endtable
endmodule

module top (a, b, o);
  input a, b;
  output o;
  t_gate(a, b);
  t_mod u_mod (o, a);
endmodule
