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

module t (/*AUTOARG*/);

   initial begin
      automatic ParclsDefaultType#(Cls) pdt1 = new;
      automatic ParclsDefaultType#(cls_t) pdt2 = pdt1;
      automatic ParclsDefaultType#(cls2_t) pdt3 = pdt2;
      automatic Parcls#(Cls) p1 = new;
      automatic Parcls#(cls_t) p2 = p1;
      automatic Parcls#(cls2_t) p3 = p2;

      if (pdt1 != pdt2) $stop;
      if (pdt2 != pdt3) $stop;
      if (p1 != p2) $stop;
      if (p2 != p3) $stop;

      if (p1.get_p() != 20) $stop;
      if (pdt1.get_p() != 20) $stop;
      if (Parcls#(cls2_t)::get_p() != 20) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
