// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef enum {ZERO, ONE, TWO} e_t;

   typedef enum {THREE=3, FOUR, FIVE} o_t;

   typedef struct packed {
      e_t m_e;
      o_t m_o;
   } struct_t;

   initial begin
      e_t e;
      o_t o;
      struct_t str;

      e = ONE;
      e = e_t'(1);
      e = e;

      e = 1;  // Bad
      o = e;  // Bad

      str.m_e = ONE;
      str.m_o = THREE;
      e = str.m_e;
      o = str.m_o;
      o = str.m_e;  // Bad

   end
endmodule
