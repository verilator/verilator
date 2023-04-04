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
   function void call_int_fn ();
     int local_i;

     local_i = get_methoda();
     if (local_i != 30) $stop;
     local_i++;
     local_i = get_methoda;
     if (local_i != 30) $stop;
   endfunction : call_int_fn

endclass : Cls

module t (/*AUTOARG*/);

   initial begin
      Cls c;
      if (c != null) $stop;
      c = new;
      c.imembera = 10;
      if (c.get_methoda() != 10) $stop;
      c.set_methoda(20);
      if (c.get_methoda() != 20) $stop;
      c.setv_methoda(30);
      if (c.get_methoda() != 30) $stop;
      if (c.get_methoda != 30) $stop;
      c.call_int_fn;
      c.call_int_fn();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
