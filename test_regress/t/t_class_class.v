// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Note UVM internals do not require classes-in-classes
package P;
class Cls #(type STORE_T=string);
   STORE_T imembera;
   STORE_T imemberb;
   class SubCls;
      STORE_T smembera;
      STORE_T smemberb;
      // TODO put extern function here or in t_class_extern.v to check link
   endclass : SubCls
   SubCls sc;
endclass : Cls
endpackage : P

module t (/*AUTOARG*/);
   P::Cls#(int) c;
   initial begin
      c = new;
      c.imembera = 10;
      c.imemberb = 20;
      c.sc = new;
      c.sc.smembera = 30;
      c.sc.smemberb = 40;
      if (c.imembera != 10) $stop;
      if (c.imemberb != 20) $stop;
      if (c.sc.smembera != 30) $stop;
      if (c.sc.smemberb != 40) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
