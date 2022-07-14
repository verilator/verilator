// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire (weak0, weak1) a = 'z;

   always begin
      if (a === 1'z) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
