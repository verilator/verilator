// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class c1;
	int c1_f;
endclass
class c2;
	int c2_f;
endclass

class Cls;
   rand int x;
   rand enum {
      ONE_Y,
      TWO_Y
   } y;
   virtual function int get_x();
      return x;
   endfunction
endclass
class SubA extends Cls;
   c1 e = new;
   enum {
      AMBIG,
      ONE_A,
      TWO_A
   } en;
   function c1 get_c();
      return e;
   endfunction
endclass
class SubB extends Cls;
   c2 e = new;
   enum {
      AMBIG,
      ONE_B,
      TWO_B
   } en;
   SubA f = new;
   function c2 get_c();
      return e;
   endfunction
   function int doit;
      // access ambiguous names so width complains if we miss something
      doit = 1;

      f.x = 4;
      x = 5;
      doit = f.randomize() with { x == local::x; };
      if (f.x != x) $stop;

      doit &= f.randomize() with { e.c1_f == local::e.c2_f; };
      doit &= f.randomize() with { get_x() == local::get_x(); };
      doit &= f.randomize() with { get_c().c1_f == local::get_c().c2_f; };
      doit &= f.randomize() with { (get_c).c1_f == (local::get_c).c2_f; };
      doit &= f.randomize() with { (get_c).c1_f == (local::get_c).c2_f; };
      doit &= f.randomize() with { y == local::y; };
      doit &= f.randomize() with { en == AMBIG; };
      f.en = SubA::ONE_A;
      doit &= f.randomize() with { en == ONE_A; };
      doit &= f.randomize() with { local::en == local::AMBIG; };
      en = ONE_B;
      doit &= f.randomize() with { local::en == ONE_B; };
   endfunction
endclass

module t (/*AUTOARG*/);
   SubB obj = new;

   initial begin
      if (obj.doit != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
