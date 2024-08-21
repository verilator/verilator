// DESCRIPTION: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

typedef enum bit[15:0] {
   ONE   = 3,
   TWO   = 5,
   THREE = 8,
   FOUR  = 13
} Enum;

typedef struct packed {
   int  a;
   bit  b;
   Enum c;
} StructInner;

typedef struct packed {
   bit         x;
   StructInner s;
   Enum        y;
   longint     z;
} StructOuter;

typedef struct {
   int         i;
   StructOuter j;
   Enum        k;
   longint     z;
} StructUnpacked;

class BaseCls1;
endclass

class Inner;
   rand logic[7:0] a;
   rand logic[15:0] b;
   rand logic[3:0] c;
   rand logic[11:0] d;
   int e;

   function new;
      a = 0;
      b = 0;
      c = 0;
      d = 0;
      e = 0;
   endfunction

endclass

class DerivedCls1 extends BaseCls1;
   rand Inner i;
   rand int j;
   int k;
   rand Enum l;

   function new;
      i = new;
      j = 0;
      k = 0;
      l = ONE;
   endfunction

endclass

class BaseCls2;
   rand int i;

   function new;
      i = 0;
   endfunction
endclass

class DerivedCls2 extends BaseCls2;
   rand int j;

   function new;
      super.new;
      j = 0;
   endfunction
endclass


class OtherCls;
   logic[63:0] v;
   rand logic[63:0] w;
   rand logic[47:0] x;
   rand logic[31:0] y;
   rand logic[23:0] z;
   rand StructUnpacked str;

   function new;
      v = 0;
      w = 0;
      x = 0;
      y = 0;
      z = 0;
      str.i = 0;
      str.j = '{x: 1'b0, y: ONE, z: 64'd0, s: '{a: 32'd0, b: 1'b0, c: ONE}};
      str.k = ONE;
   endfunction

endclass

class ContainsNull;
   rand BaseCls1 b;
endclass

class ClsWithInt;
   rand int a;
   int b;
endclass

class DeriveClsWithInt extends ClsWithInt;
endclass

class DeriveAndContainClsWithInt extends ClsWithInt;
   rand ClsWithInt cls1;
   ClsWithInt cls2;
   function new;
      cls1 = new;
      cls2 = new;
   endfunction
endclass

class ClsUsedOnlyHere;
   rand int a;
endclass

typedef ClsUsedOnlyHere cls_used_only_here_t;

class ClsContainUsedOnlyHere;
   rand cls_used_only_here_t c;
   function new;
      c = new;
   endfunction
endclass

module t (/*AUTOARG*/);

   DerivedCls1 derived1;
   DerivedCls2 derived2;
   OtherCls other;
   BaseCls1 base;
   ContainsNull cont;
   DeriveClsWithInt der_int;
   DeriveAndContainClsWithInt der_contain;
   ClsContainUsedOnlyHere cls_cont_used;

   initial begin
      derived1 = new;
      derived2 = new;
      other = new;
      cont = new;
      der_int = new;
      der_contain = new;
      base = derived1;
      cls_cont_used = new;
      for (int i = 0; i < 10; i++) begin
         void'(base.randomize());
         void'(derived2.randomize());
         void'(other.randomize());
         void'(cont.randomize());
         void'(der_int.randomize());
         void'(der_contain.randomize());
         if (!(derived1.l inside {ONE, TWO, THREE, FOUR})) $stop;
         if (!(other.str.j.s.c inside {ONE, TWO, THREE, FOUR})) $stop;
         if (!(other.str.j.y inside {ONE, TWO, THREE, FOUR})) $stop;
         if (!(other.str.k inside {ONE, TWO, THREE, FOUR})) $stop;
         if (derived1.i.e != 0) $stop;
         if (derived1.k != 0) $stop;
         if (other.v != 0) $stop;
         if (cont.b != null) $stop;
         if (der_int.b != 0) $stop;
         if (der_contain.cls2.a != 0) $stop;
         if (der_contain.cls1.b != 0) $stop;
         if (der_contain.b != 0) $stop;
      end
      `check_rand(derived1, derived1.i.a);
      `check_rand(derived1, derived1.i.b);
      `check_rand(derived1, derived1.i.c);
      `check_rand(derived1, derived1.j);
      `check_rand(derived1, derived1.l);
      `check_rand(derived2, derived2.i);
      `check_rand(derived2, derived2.j);
      `check_rand(other, other.w);
      `check_rand(other, other.x);
      `check_rand(other, other.y);
      `check_rand(other, other.z);
      `check_rand(other, other.str.i);
      `check_rand(other, other.str.j.x);
      `check_rand(other, other.str.j.y);
      `check_rand(other, other.str.j.z);
      `check_rand(other, other.str.j.s.a);
      `check_rand(other, other.str.j.s.b);
      `check_rand(other, other.str.j.s.c);
      `check_rand(other, other.str.k);
      `check_rand(der_int, der_int.a);
      `check_rand(der_contain, der_contain.cls1.a);
      `check_rand(der_contain, der_contain.a);
      `check_rand(cls_cont_used, cls_cont_used.c.a);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
