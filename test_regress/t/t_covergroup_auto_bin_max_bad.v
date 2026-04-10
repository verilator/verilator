// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   int size_var;
   logic [3:0] cp_expr;

   // Error: option.auto_bin_max must be a constant expression (group level)
   covergroup cg;
      option.auto_bin_max = size_var;
      cp: coverpoint cp_expr;
   endgroup

   cg cg_i = new;
   initial $finish;
endmodule
