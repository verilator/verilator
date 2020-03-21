// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o, oa, ro, roa, wo, woa, vo, voa
   );

   wire w;
   reg  r;
   output o;
   output [1:0] oa;
   output reg ro;
   output reg [1:0] roa;
   output wire wo;
   output wire [1:0] woa;
   // 1800 only
   output var vo;
   output var [1:0] voa;

   initial begin
      w = '0;  // Error
      o = '0;  // Error
      oa = '0;  // Error
      wo = '0;  // Error
      woa = '0;  // Error
      r = '0;  // Not an error
      ro = '0;  // Not an error
      roa = '0;  // Not an error
      vo = '0;  // Not an error
      voa = '0;  // Not an error
   end

endmodule
