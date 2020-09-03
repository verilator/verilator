// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Base0;
   // No members to check that to_string handles this
endclass

class Base1 extends Base0;
   int b1member;
   typedef int T;
endclass

class Base2 extends Base1;
   int b2member;
endclass

class Cls extends Base2;
   int imembera;
   int imemberb;
   T imemberc;
endclass : Cls

class uvm_object_wrapper;
  function int create ();
  endfunction
endclass

class uvm__registry #(type T=int) extends uvm_object_wrapper;
  // This override must be in the new symbol table, not
  // under the extend's symbol table
  function int create ();
    T obj;
  endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.b1member = 10;
      c.b2member = 30;
      c.imembera = 100;
      c.imemberb = 110;
      c.imemberc = 120;
      $display("Display: set = \"%p\"", c);  // '{all 4 members}
      if (c.b1member != 10) $stop;
      if (c.b2member != 30) $stop;
      if (c.imembera != 100) $stop;
      if (c.imemberb != 110) $stop;
      if (c.imemberc != 120) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
