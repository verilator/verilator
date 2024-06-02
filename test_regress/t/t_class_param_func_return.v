// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo #(type T=int);
   typedef Foo default_type;
   typedef Foo#(T) this_type;

   T x;

   function default_type get_default();
      default_type o = new;
      return o;
   endfunction

   function this_type get_this();
      this_type o = new;
      return o;
   endfunction
endclass

module t (/*AUTOARG*/);

   Foo f_def1, f_def2;
   Foo#(bit) f_bit1, f_bit2;
   initial begin
      f_def1 = new;
      f_bit1 = new;

      f_def2 = f_def1.get_default();
      if ($bits(f_def2.x) != 32) $stop;
      f_def2 = f_def1.get_this();
      if ($bits(f_def2.x) != 32) $stop;

      f_def2 = f_bit1.get_default();
      if ($bits(f_def2.x) != 32) $stop;
      f_bit2 = f_bit1.get_this();
      if ($bits(f_bit2.x) != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
