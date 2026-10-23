// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 29.3.1: All ports of a UDP shall be scalar

primitive p_comb (o, a, b, c);
  output o;
  input [0:0] a;  // <--- BAD
  input integer b;  // <--- BAD
  input [0:0][0:0] c;  // <--- BAD
  table
    1 ? ? : 1;
    0 ? ? : 0;
  endtable
endprimitive

primitive p_seq (q, d);
  output q;
  reg [0:0] q;  // <--- BAD
  input d;
  table
    r : ? : 1;
  endtable
endprimitive

primitive p_ansi (output reg [0:0] q, input d);  // <--- BAD
  table
    r : ? : 1;
  endtable
endprimitive

module t (
    input a,
    input integer i,
    output o,
    output q_seq,
    output q_ansi
);
  p_comb u_comb (o, a, i, a);
  p_seq u_seq (q_seq, a);
  p_ansi u_ansi (q_ansi, a);
endmodule
