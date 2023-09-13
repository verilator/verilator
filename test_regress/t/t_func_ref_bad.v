// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   function bit get_x(ref bit x);
      return x;
   endfunction
endclass

module t (/*AUTOARG*/);
   bit [10:0] a;
   bit b;
   Cls cls;
   initial begin
      cls = new;
      b = cls.get_x(a[1]);
      $stop;
   end
endmodule
