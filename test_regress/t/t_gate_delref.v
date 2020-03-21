// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug1475
module t (/*AUTOARG*/
   // Outputs
   ID_45, IDa_f4c,
   // Inputs
   clk, ID_d9f, IDa_657, ID_477
   );
   input clk;
   output reg ID_45;
   input      ID_d9f;
   input      IDa_657;
   output reg IDa_f4c;

   reg        ID_13;
   input      ID_477;
   reg        ID_489;
   reg        ID_8d1;
   reg        IDa_183;
   reg        IDa_91c;
   reg        IDa_a96;
   reg        IDa_d6b;
   reg        IDa_eb9;
   wire ID_fc8 = ID_d9f & ID_13;  //<<
   wire ID_254 = ID_d9f & ID_13;
   wire ID_f40 = ID_fc8 ? ID_8d1 : 0;
   wire ID_f4c = ID_fc8 ? 0 : ID_477;
   wire ID_442 = IDa_91c;
   wire ID_825 = ID_489;
   always @(posedge clk) begin
      ID_13 <= ID_f40;
      ID_8d1 <= IDa_eb9;
      ID_489 <= ID_442;
      ID_45 <= ID_825;
      IDa_d6b <= IDa_a96;
      IDa_f4c <= ID_f4c;
      if (ID_254) begin
         IDa_91c <= IDa_d6b;
         IDa_183 <= IDa_657;
         IDa_a96 <= IDa_657;
         IDa_eb9 <= IDa_183;
      end
   end
endmodule
