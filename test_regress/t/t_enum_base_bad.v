// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   typedef struct {
      int a;
   } s_t;

   typedef enum s_t {
                     EN_ZERO } bad_t;

   typedef int int_t;

   typedef enum int_t { EN_ONE = 1 } ok1_t;

   s_t s;
   int_t i;

endmodule
