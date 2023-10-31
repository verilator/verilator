// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int x;
   function new;
      x = 10;
   endfunction
   function bit set_x(int a);
      x = a;
      return 1;
   endfunction
   function int get_x;
      return x;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls cls;
      if (cls != null && cls.x == 10) $stop;
      if (cls != null && cls.get_x() == 10) $stop;
      cls = new;
      if (!cls.set_x(1) || cls.x != 1) $stop;
      if (!cls.set_x(2) || cls.get_x() != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
