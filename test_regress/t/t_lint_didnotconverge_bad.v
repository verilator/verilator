// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   a, b
   );

   // verilator lint_off UNOPT

   output logic a, b;

   always_comb b = ~a;
   always_comb a = b;

endmodule
