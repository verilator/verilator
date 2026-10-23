// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 29.8: UDP instance terminals connect by position only

primitive p_and (o, a, b);
  output o;
  input a, b;
  table
    1 1 : 1;
    0 ? : 0;
    ? 0 : 0;
  endtable
endprimitive

module t (
    input a,
    input b,
    output o,
    output o_name,
    output o_pos
);
  p_and u_name (.o(o_name), .a(a), .b(b));  // <--- BAD
  p_and u_star (.*);  // <--- BAD
  p_and u_pos (o_pos, a, b);
endmodule
