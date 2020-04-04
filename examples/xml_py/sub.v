// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

module sub
  #(parameter type TYPE_t = logic)
   (
    input TYPE_t in,
    output TYPE_t out
    );

   // Some simple logic
   always_comb out = ~ in;

endmodule
