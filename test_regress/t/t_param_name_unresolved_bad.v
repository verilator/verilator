// DESCRIPTION: Verilator: Verilog Test module
//
// Errors for a parameter that another parameter's type depends on, when its value
// can't be worked out.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH

module m_none #(
    parameter int N,
    parameter logic [N:0] P = '0
) ();
endmodule

module m_cycle #(
    parameter int A = B,
    parameter int B = A,
    parameter logic [A:0] P = '0
) ();
endmodule

module t;
  m_none #(.P(3'd5)) i_none ();  // No value
  m_cycle #(.P(3'd5)) i_cycle ();  // Circular
endmodule
