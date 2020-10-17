// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      int q[int];
      int qe[$];
      int qv[$];
      int i;
      string v;

      q = '{10:1, 11:2, 12:2, 13:4, 14:3};
      v = $sformatf("%p", q); `checks(v, "'{0xa:1, 0xb:2, 0xc:2, 0xd:4, 0xe:3} ");

      // NOT tested: with ... selectors

      //q.sort;  // Not legal on assoc - see t_assoc_meth_bad
      //q.rsort;  // Not legal on assoc - see t_assoc_meth_bad
      //q.reverse;  // Not legal on assoc - see t_assoc_meth_bad
      //q.shuffle;  // Not legal on assoc - see t_assoc_meth_bad

      qv = q.unique;
      v = $sformatf("%p", qv); `checks(v, "'{1, 2, 4, 3} ");
      qv = qe.unique;
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.unique_index; qv.sort;
      v = $sformatf("%p", qv); `checks(v, "'{10, 11, 13, 14} ");

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
      qv = q.find with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{2, 2} ");
      qv = q.find_index with (item == 2); qv.sort;
      v = $sformatf("%p", qv); `checks(v, "'{11, 12} ");
      qv = q.find_first with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{2} ");
      qv = q.find_first_index with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{11} ");
      qv = q.find_last with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{2} ");
      qv = q.find_last_index with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{12} ");

      qv = q.find with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_index with (item == 20); qv.sort;
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_first with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_first_index with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_last with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_last_index with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");

      qv = q.min;
      v = $sformatf("%p", qv); `checks(v, "'{1} ");
      qv = q.max;
      v = $sformatf("%p", qv); `checks(v, "'{4} ");

      qv = qe.min;
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = qe.max;
      v = $sformatf("%p", qv); `checks(v, "'{}");

      // Reduction methods

      i = q.sum; `checkh(i, 32'hc);
      i = q.sum with (item + 1); `checkh(i, 32'h11);
      i = q.product; `checkh(i, 32'h30);
      i = q.product with (item + 1); `checkh(i, 32'h168);

      i = qe.sum; `checkh(i, 32'h0);
      i = qe.product; `checkh(i, 32'h0);

      q = '{10:32'b1100, 11:32'b1010};
      i = q.and; `checkh(i, 32'b1000);
      i = q.and with (item + 1); `checkh(i, 32'b1001);
      i = q.or; `checkh(i, 32'b1110);
      i = q.or with (item + 1); `checkh(i, 32'b1111);
      i = q.xor; `checkh(i, 32'b0110);
      i = q.xor with (item + 1); `checkh(i, 32'b0110);

      i = qe.and; `checkh(i, 32'b0);
      i = qe.or; `checkh(i, 32'b0);
      i = qe.xor; `checkh(i, 32'b0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
