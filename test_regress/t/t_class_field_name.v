// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int queue;
endclass

module t;

   initial begin
      Cls cls = new;
      cls.queue = 1;
      if (cls.queue == 1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
