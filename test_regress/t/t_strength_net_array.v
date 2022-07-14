// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire [7:0] a;
   assign (strong0, weak1) a = 8'hac;
   assign (pull0, pull1) a = '1;

   always begin
      if (a == 8'hac) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
