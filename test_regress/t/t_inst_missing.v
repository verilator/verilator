// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire ok = 1'b0;
   // verilator lint_off PINNOCONNECT
   // verilator lint_off PINCONNECTEMPTY
   sub sub (.ok(ok), , .nc());
   // verilator lint_on PINCONNECTEMPTY
   // verilator lint_on PINNOCONNECT
endmodule

module sub (input ok, input none, input nc);
   initial if (ok && none && nc) begin end  // No unused warning
endmodule
