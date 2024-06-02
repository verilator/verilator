// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
endclass : Cls

typedef struct {
   Cls obj;
   int number;
} str_t;

module t (/*AUTOARG*/);
   function automatic str_t func_null();
      return '{null, 42};
   endfunction

   function automatic str_t func_obj();
      Cls c;
      c = new;
      return '{c, 43};
   endfunction

   initial begin
      str_t result;
      result = func_null();
      if (result.obj != null) $stop;
      if (result.number != 42) $stop;

      result = func_obj();
      if (result.obj == null) $stop;
      if (result.number != 43) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
