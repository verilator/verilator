// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
class Base0;
   class BaseInnerOnly;
     int inneronly;
     function new();
       inneronly = 10;
       if (inneronly != 10) $stop;
     endfunction
   endclass

   class BaseInnerOver;
     int innerover;
     function new();
       innerover = 10;
       if (innerover != 10) $stop;
     endfunction
   endclass

   int baseonly;
   int baseover;
   BaseInnerOnly inneronly = new;
   BaseInnerOver innerover = new;

   function void b_set_bo(int v); baseover = v; endfunction
   function int b_get_bo(); return baseover; endfunction
   function int get_bo(); return baseover; endfunction
   function void b_set_io(int v); innerover.innerover = v; endfunction
   function int b_get_io(); return innerover.innerover; endfunction
   function int get_io(); return innerover.innerover; endfunction
endclass
endpackage

// We need to import Base0, as verilator currently doesn't support
// multiple `::` references, but we would need to do that to reference
// `BaseInnerOnly` class inside `Ext` class.
import Pkg::Base0;
class Ext extends Pkg::Base0;
   class BaseInnerOver;
     int innerover;
     function new();
       innerover = 20;
       if (innerover != 20) $stop;
     endfunction
   endclass
   int baseover;
   int extonly;
   BaseInnerOnly inneronly = new;
   BaseInnerOver innerover = new;

   function void e_set_bo(int v); baseover = v; endfunction
   function int e_get_bo(); return baseover; endfunction
   function int get_bo(); return baseover; endfunction
   function void e_set_io(int v); innerover.innerover = v; endfunction
   function int e_get_io(); return innerover.innerover; endfunction
   function int get_io(); return innerover.innerover; endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Ext c;
      c = new;
      c.baseonly = 10;
      c.baseover = 20;
      c.extonly = 30;
      c.inneronly.inneronly = 40;
      c.innerover.innerover = 50;
      if (c.baseonly != 10) $stop;
      if (c.baseover != 20) $stop;
      if (c.extonly != 30) $stop;
      if (c.inneronly.inneronly != 40) $stop;
      if (c.innerover.innerover != 50) $stop;

      c.b_set_bo(100);
      c.e_set_bo(200);
      c.b_set_io(300);
      c.e_set_io(400);
      if (c.b_get_bo() != 100) $stop;
      if (c.e_get_bo() != 200) $stop;
      if (c.get_bo() != 200) $stop;
      if (c.b_get_io() != 300) $stop;
      if (c.e_get_io() != 400) $stop;
      if (c.get_io() != 400) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
