// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (/*AUTOARG*/);

   int a1[2] = '{12, 13};
   int a2[2] = {14, 15};
   int a3[1] = '{16};
   int a4[1] = {17};

   initial begin
      `checkh(a1[0], 12);
      `checkh(a1[1], 13);

      `checkh(a2[0], 14);
      `checkh(a2[1], 15);

      `checkh(a3[0], 16);

      `checkh(a4[0], 17);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
