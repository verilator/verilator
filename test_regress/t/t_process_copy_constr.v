// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int x = 1;
   function new();
      int p = process::self();
   endfunction
endclass

module t (/*AUTOARG*/
   );
   initial begin
      Cls c, d;
      c = new;
      c.x = 2;
      d = new c;
      if (d.x != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
