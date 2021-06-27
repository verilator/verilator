// DESCRIPTION: Verilator: Verilog Test module for specialized type default values
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Andrej Korman.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off UNPACKED */

module t;
   typedef struct packed {
      bit       a;
      bit       b;
      bit       c;
      bit       d;
   } helper_type1;

   const helper_type1 ex1 = '{default: 1'b0, default: 1'b1};
endmodule
