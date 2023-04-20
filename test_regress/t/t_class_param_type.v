// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// See also t_class_param.v

class Parcls #(type T);
   static function int get_p;
     return T::get_p();
   endfunction
endclass

class Cls;
   static function int get_p;
     return 20;
   endfunction
endclass

class ParclsDefaultType #(type T=Cls);
   static function int get_p;
     return T::get_p();
   endfunction
endclass

typedef Cls cls_t;
typedef cls_t cls2_t;

class Singleton #(type T=int);
   static function Singleton#(T) self;
      static Singleton#(T) c = new;
      return c;
   endfunction
   function int get_size;
      return $bits(T);
   endfunction
endclass

class SingletonUnusedDefault #(type T=int);
   static function SingletonUnusedDefault#(T) self;
      static SingletonUnusedDefault#(T) c = new;
      return c;
   endfunction
endclass

class Empty;
endclass

class Foo #(type IF=Empty) extends IF;
   typedef Foo foo_t;
   int a = 1;
endclass

class Bar #(type A=int, type B=A) extends Foo;
   function int get_size_A;
      return $bits(A);
   endfunction
   function int get_size_B;
      return $bits(B);
   endfunction
endclass

class Empty2;
endclass

class Baz #(type T=Empty2) extends Foo;
endclass

class Getter1 extends Baz;
   function int get_1;
      foo_t f = new;
      return f.a;
   endfunction
endclass

module t (/*AUTOARG*/);

   initial begin
      automatic ParclsDefaultType#(Cls) pdt1 = new;
      automatic ParclsDefaultType#(cls_t) pdt2 = pdt1;
      automatic ParclsDefaultType#(cls2_t) pdt3 = pdt2;
      automatic Parcls#(Cls) p1 = new;
      automatic Parcls#(cls_t) p2 = p1;
      automatic Parcls#(cls2_t) p3 = p2;

      automatic Singleton #(int) s_int1 = Singleton#(int)::self();
      automatic Singleton #(int) s_int2 = Singleton#(int)::self();
      automatic Singleton #(bit) s_bit1 = Singleton#(bit)::self();
      automatic Singleton #(bit) s_bit2 = Singleton#(bit)::self();
      automatic SingletonUnusedDefault #(bit) sud1 = SingletonUnusedDefault#(bit)::self();
      automatic SingletonUnusedDefault #(bit) sud2 = SingletonUnusedDefault#(bit)::self();

      automatic Getter1 getter1 = new;

      typedef bit my_bit_t;
      Bar#(.A(my_bit_t)) bar_a_bit = new;
      Bar#(.B(my_bit_t)) bar_b_bit = new;
      Bar#() bar_default = new;

      if (bar_a_bit.get_size_A != 1) $stop;
      if (bar_a_bit.get_size_B != 1) $stop;
      if (bar_b_bit.get_size_A != 32) $stop;
      if (bar_b_bit.get_size_B != 1) $stop;
      if (bar_default.get_size_A != 32) $stop;
      if (bar_default.get_size_B != 32) $stop;

      if (pdt1 != pdt2) $stop;
      if (pdt2 != pdt3) $stop;
      if (p1 != p2) $stop;
      if (p2 != p3) $stop;

      if (s_int1 != s_int2) $stop;
      if (s_bit1 != s_bit2) $stop;
      if (sud1 != sud2) $stop;

      if (s_int1.get_size() != 32) $stop;
      if (s_bit1.get_size() != 1) $stop;

      if (p1.get_p() != 20) $stop;
      if (pdt1.get_p() != 20) $stop;
      if (Parcls#(cls2_t)::get_p() != 20) $stop;

      if (getter1.get_1() != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
