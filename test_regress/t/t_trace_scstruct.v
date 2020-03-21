// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNUSED
// verilator lint_off UNDRIVEN

//bug858

typedef struct packed {
    logic m_1;
    logic m_2;
} struct_t;

typedef struct packed {
    logic [94:0] m_1;
    logic m_2;
} struct96_t;

module t
  (
   input struct_t   test_input,
   input struct96_t t96
   );
endmodule
