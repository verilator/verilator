// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inouts
   AVDD, AVSS
   );
   inout AVDD;
   inout  AVSS;

   sub sub (/*AUTOINST*/
            // Inouts
            .AVDD                       (AVDD),
            .AVSS                       (AVSS));

   initial begin
         $write("*-* All Finished *-*\n");
         $finish;
   end
endmodule

module sub (/*AUTOARG*/
   // Inouts
   AVDD, AVSS
   );
   // verilator no_inline_module
   inout AVDD;
   inout AVSS;
   tri NON_IO;
   initial if (NON_IO !== 'z) $stop;
endmodule
