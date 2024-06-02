// DESCRIPTION: Verilator: Verilog Test module
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

class BaseCls;
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

class DerivedCls extends BaseCls;
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

class OtherCls;
   logic[63:0] v;
   rand logic[63:0] w;
   rand logic[47:0] x;
   rand logic[31:0] y;
   rand logic[23:0] z;
   rand StructOuter str;

   function new;
      v = 0;
      w = 0;
      x = 0;
      y = 0;
      z = 0;
      str = '{x: 1'b0, y: ONE, z: 64'd0, s: '{a: 32'd0, b: 1'b0, c: ONE}};
   endfunction

endclass

class ContainsNull;
   rand BaseCls b;
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

   DerivedCls derived;
   OtherCls other;
   BaseCls base;
   ContainsNull cont;
   DeriveClsWithInt der_int;
   DeriveAndContainClsWithInt der_contain;
   ClsContainUsedOnlyHere cls_cont_used;

   initial begin
      int rand_result;
      derived = new;
      other = new;
      cont = new;
      der_int = new;
      der_contain = new;
      base = derived;
      cls_cont_used = new;
      for (int i = 0; i < 10; i++) begin
         rand_result = base.randomize();
         rand_result = other.randomize();
         rand_result = cont.randomize();
         rand_result = der_int.randomize();
         rand_result = der_contain.randomize();
         if (!(derived.l inside {ONE, TWO, THREE, FOUR})) $stop;
         if (!(other.str.s.c inside {ONE, TWO, THREE, FOUR})) $stop;
         if (!(other.str.y inside {ONE, TWO, THREE, FOUR})) $stop;
         if (derived.i.e != 0) $stop;
         if (derived.k != 0) $stop;
         if (other.v != 0) $stop;
         if (cont.b != null) $stop;
         if (der_int.b != 0) $stop;
         if (der_contain.cls2.a != 0) $stop;
         if (der_contain.cls1.b != 0) $stop;
         if (der_contain.b != 0) $stop;
      end
      `check_rand(derived, derived.i.a);
      `check_rand(derived, derived.i.b);
      `check_rand(derived, derived.i.c);
      `check_rand(derived, derived.j);
      `check_rand(derived, derived.l);
      `check_rand(other, other.w);
      `check_rand(other, other.x);
      `check_rand(other, other.y);
      `check_rand(other, other.z);
      `check_rand(other, other.str.x);
      `check_rand(other, other.str.y);
      `check_rand(other, other.str.z);
      `check_rand(other, other.str.s.a);
      `check_rand(other, other.str.s.b);
      `check_rand(other, other.str.s.c);
      `check_rand(der_int, der_int.a);
      `check_rand(der_contain, der_contain.cls1.a);
      `check_rand(der_contain, der_contain.a);
      `check_rand(cls_cont_used, cls_cont_used.c.a);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
