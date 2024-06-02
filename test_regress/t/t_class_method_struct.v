// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   int         x;
   int         y;
   int         z;
} my_struct;

class Cls;
   function my_struct get_struct;
      my_struct s;
      s.x = 1;
      s.y = 2;
      s.z = 3;
      return s;
   endfunction
endclass : Cls

module t (/*AUTOARG*/);
   initial begin
      Cls c = new;
      my_struct s = c.get_struct;
      if (s.x != 1) $stop;
      if (s.y != 2) $stop;
      if (s.z != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
