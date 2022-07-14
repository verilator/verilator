// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire (weak0, weak1) a = 1;
   assign (strong0, strong1) a = 0;

   always begin
      if (!a) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
