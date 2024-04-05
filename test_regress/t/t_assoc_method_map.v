// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/);

   initial begin
      int res[];
      int a[int] = '{1: 100, 2: 200, 3: 300};

      // TODO results not known to be correct
      res = a.map(el) with (el == 2);
      `checkh(res.size, 3);
      `checkh(res[0], 0);
      `checkh(res[1], 1);
      `checkh(res[2], 0);
   end
endmodule
