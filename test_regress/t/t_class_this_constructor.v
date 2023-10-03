// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   bit x = 1'b0;
   function new;
      Cls c;
      if (c == this) begin
         x = 1'b1;
      end
   endfunction
endclass

module t (/*AUTOARG*/);
   Cls c;
   initial begin
      c = new;
      if (c.x) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
