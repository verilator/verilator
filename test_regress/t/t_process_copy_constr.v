// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int x = 1;
   function new();
      process p = process::self();
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
