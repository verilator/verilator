// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

function int get_val_set_5(ref int x);
   automatic int y = x;
   x = 5;
   return y;
endfunction

module t (/*AUTOARG*/);
   initial begin
      int a = 10;
      int b = get_val_set_5(a);
      `checkh(a, 5);
      `checkh(b, 10);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
