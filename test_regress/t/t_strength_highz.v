// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire (weak0, highz1) a = 1;
   wire (strong1, highz0) b = 0;
   wire (highz0, pull1) c = 0;
   wire (highz1, supply0) d = 1;

   always begin
      if (a === 1'bz && b === 1'bz && c === 1'bz && d === 1'bz) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
