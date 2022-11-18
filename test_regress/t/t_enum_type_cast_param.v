// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef enum {ZERO, ONE, TWO} e_t;

   localparam e_t param_enum = e_t'(0);

endmodule
