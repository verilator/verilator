// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      int q[5];
      int qv[$];  // Value returns
      int qi[$];  // Index returns
      int i;
      string v;

      q = '{1, 2, 2, 4, 3};
      v = $sformatf("%p", q); `checks(v, "'{1, 2, 2, 4, 3} ");

      // Reduction methods

      i = q.sum with (item + 1); `checkh(i, 32'h11);
      i = q.product with (item + 1); `checkh(i, 32'h168);

      q = '{32'b1100, 32'b1010, 32'b1100, 32'b1010, 32'b1010};
      i = q.and with (item + 1); `checkh(i, 32'b1001);
      i = q.or with (item + 1); `checkh(i, 32'b1111);
      i = q.xor with (item + 1); `checkh(i, 32'hb);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
