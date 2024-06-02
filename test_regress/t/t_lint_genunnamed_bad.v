// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   parameter P = 1;

   if (P) ;

   if (P)
     begin
        initial $display;
     end
   else
     begin
        initial $display;
     end

   for (genvar v = 0; v < P; ++v) ;

   for (genvar v = 0; v < P; ++v)
     begin
        initial $display;
     end

   case (P)
     1: initial begin end
     2: begin
        initial begin end
     end
   endcase

endmodule
