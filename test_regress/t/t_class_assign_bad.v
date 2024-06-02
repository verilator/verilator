// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
endclass : Cls

class Cls2;
endclass

class ClsExt extends Cls;
endclass

typedef Cls2 cls2_t;

module t (/*AUTOARG*/);
   Cls c;
   Cls2 c2;
   cls2_t ct2;
   ClsExt c_ext;

   task t(Cls c); endtask
   function f(ClsExt c); endfunction

   initial begin
      c = 0;
      c = 1;
      c = c2;
      c_ext = c;
      ct2 = c;

      t(0);
      t(1);
      t(c2);
      f(c);
   end
endmodule
