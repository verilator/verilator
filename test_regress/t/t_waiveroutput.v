// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_waiveroutput;
   reg width_warn = 2'b11;  // Width warning - must be line 8

   // verilator lint_off UNUSEDSIGNAL
   // verilator lint_off WIDTHTRUNC
   reg width_warn2 = 2'b11;
   // verilator lint_on UNUSEDSIGNAL
   // verilator lint_on WIDTHTRUNC
endmodule
