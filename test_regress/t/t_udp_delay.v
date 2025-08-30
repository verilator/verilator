// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

primitive not_u(out, in);
  output out;
  input in;
  table
    0 : 1;
    1 : 0;
  endtable
endprimitive

module t (out, in);
  input in;
  output wire out;
  real v = 0.34;
  not_u #(1.145, v) dut_u (out, in);
endmodule
