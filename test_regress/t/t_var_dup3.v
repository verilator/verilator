// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Legal with Verilog 1995 style ports

module t
  (/*AUTOARG*/
   // Outputs
   ok_o_w, ok_o_r, ok_o_ra, ok_or, ok_ow, ok_owa
   );

   output ok_o_w;
   wire   ok_o_w;

   output ok_o_r;
   reg    ok_o_r;

   output [1:0] ok_o_ra;
   reg    [1:0] ok_o_ra;

   output reg ok_or;

   output wire ok_ow;

   output wire [1:0] ok_owa;
endmodule
