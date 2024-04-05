// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Cls;
   bit x = 1;
endclass

module t (/*AUTOARG*/);
   Cls obj1;
   Cls obj2;

   initial begin
      obj1 = new;
      `checkh(obj1.x, 1);

      obj1.x = 0;
      obj2 = new obj1;
      `checkh(obj2.x, 0);

      obj2.x = 1;
      `checkh(obj1.x, 0);
      `checkh(obj2.x, 1);

      obj2.x = 0;
      `checkh(obj2.x, 0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
