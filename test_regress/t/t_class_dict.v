// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Cls;
   int x;
   function new(int a);
      x = a;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      int dict[Cls];
      Cls c1 = new(1);
      Cls c2 = new(2);
      dict[c1] = 1;
      dict[c2] = 2;
      `checkh(dict[c1], 1);
      `checkh(dict[c2], 2);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
