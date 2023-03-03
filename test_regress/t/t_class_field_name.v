// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int queue;
endclass

module t (/*AUTOARG*/);

   initial begin
      Cls cls = new;
      cls.queue = 1;
      if (cls.queue == 1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
