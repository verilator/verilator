// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Arkadiusz Kozdra.
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
      Singleton#(T) c = new;
      return c;
   endfunction
   function int get_size;
      return $bits(T);
   endfunction
endclass

class SingletonUnusedDefault #(type T=int);
   static function SingletonUnusedDefault#(T) self;
      SingletonUnusedDefault#(T) c = new;
      return c;
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

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
