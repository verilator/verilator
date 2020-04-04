// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Illegal with ANSI Verilog 2001 style ports
module t
  (
   output bad_o_w,
   output bad_o_r);

   wire bad_o_w;
   reg  bad_o_r;
endmodule
