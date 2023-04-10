// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Cls;
   int imembera;
   function int get_methoda; return imembera; endfunction
   task set_methoda(input int val); imembera = val; endtask
   function void setv_methoda(input int val); imembera = val; endfunction
endclass : Cls

module t (/*AUTOARG*/);
   initial begin
     int tmp_i;
      Cls c;
      if (c != null) $stop;
      c = new;
      c.imembera = 10;
      if (c.get_methoda() != 10) $stop;
      c.set_methoda(20);
      if (c.get_methoda() != 20) $stop;
      c.setv_methoda(30);
      if (c.get_methoda() != 30) $stop;
      c.setv_methoda(300);
      tmp_i = c.get_methoda;
      if (tmp_i != 300) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
