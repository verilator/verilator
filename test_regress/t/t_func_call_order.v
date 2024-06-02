// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);
   int a;
   function int assign5;
      a = 5;
      return 5;
   endfunction
   function int assign3;
      a = 3;
      return 3;
   endfunction
   function int incr;
      a++;
      return a;
   endfunction
   function int assign5_return_arg(int x);
      a = 5;
      return x;
   endfunction
   int i;

   initial begin
      a = 1;
      i = assign5() + assign3() + incr();
      `checkd(a, 4); `checkd(i, 12);

      a = 1;
      i = assign5_return_arg(assign3()+incr());
      `checkd(a, 5); `checkd(i, 7);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
