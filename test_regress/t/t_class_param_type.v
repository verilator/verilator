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

typedef Cls cls_t;
typedef cls_t cls2_t;

module t (/*AUTOARG*/);

   initial begin
      if (Parcls#(cls2_t)::get_p() != 20) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
