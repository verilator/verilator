// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
   initial begin
      integer r = $random;
      integer ex;
      if ($value$plusargs("SEED=%x", ex) !== 1) $stop;
      `checkh(r, ex);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
