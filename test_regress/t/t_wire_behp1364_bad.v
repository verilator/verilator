// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
   output o,
   output [1:0] oa,
   output reg ro,
   output reg [1:0] roa,
   output wire wo,
   output wire [1:0] woa
   //1800 only:
   //output var vo;
   //output var [1:0] voa;
   );

   wire w;
   reg  r;

   initial begin
      // Error
      w = 0;
      o = 0;
      oa = 0;
      wo = 0;
      woa = 0;
      // Not an error
      r = 0;
      ro = 0;
      roa = 0;
      //vo = 0;
      //voa = 0;
   end

endmodule
