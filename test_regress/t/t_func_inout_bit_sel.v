// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

class Cls;
   function bit get_x_set_1(inout bit x);
      bit a = x;
      x = 1;
      return a;
   endfunction
endclass

module t (/*AUTOARG*/);
   int a;
   bit b;
   Cls cls;
   initial begin
      cls = new;
      b = cls.get_x_set_1(a[1]);
      `checkh(b, 0);
      `checkh(a[1], 1);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
