// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base0;
   int baseonly;
   int baseover;

   function void b_set_bo(int v); baseover = v; endfunction
   function int b_get_bo(); return baseover; endfunction
   function int get_bo(); return baseover; endfunction
endclass

class Ext extends Base0;
   int baseover;
   int extonly;

   function void e_set_bo(int v); baseover = v; endfunction
   function int e_get_bo(); return baseover; endfunction
   function int get_bo(); return baseover; endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Ext c;
      c = new;
      c.baseonly = 10;
      c.baseover = 20;
      c.extonly = 30;
      if (c.baseonly != 10) $stop;
      if (c.baseover != 20) $stop;
      if (c.extonly != 30) $stop;

      c.b_set_bo(100);
      c.e_set_bo(200);
      if (c.b_get_bo() != 100) $stop;
      if (c.e_get_bo() != 200) $stop;
      if (c.get_bo() != 200) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
