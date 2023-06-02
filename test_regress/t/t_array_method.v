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
      int q[5];
      int qv[$];  // Value returns
      int qi[$];  // Index returns
      int i;
      string v;

      q = '{1, 2, 2, 4, 3};
      v = $sformatf("%p", q); `checks(v, "'{1, 2, 2, 4, 3} ");

      // NOT tested: with ... selectors

      q.sort;
      v = $sformatf("%p", q); `checks(v, "'{1, 2, 2, 3, 4} ");
      q.sort with (item == 2);
      v = $sformatf("%p", q); `checks(v, "'{4, 3, 1, 2, 2} ");
      q.sort(x) with (x == 3);
      v = $sformatf("%p", q); `checks(v, "'{2, 1, 2, 4, 3} ");

      q.rsort;
      v = $sformatf("%p", q); `checks(v, "'{4, 3, 2, 2, 1} ");
      q.rsort with (item == 2);
      v = $sformatf("%p", q); `checks(v, "'{2, 2, 4, 1, 3} ");

      qv = q.unique;
      v = $sformatf("%p", qv); `checks(v, "'{2, 4, 1, 3} ");
      qi = q.unique_index; qi.sort;
      v = $sformatf("%p", qi); `checks(v, "'{0, 2, 3, 4} ");
      q.reverse;
      v = $sformatf("%p", q); `checks(v, "'{3, 1, 4, 2, 2} ");
      q.shuffle(); q.sort;
      v = $sformatf("%p", q); `checks(v, "'{1, 2, 2, 3, 4} ");

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
      qv = q.find with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{2, 2} ");
      qv = q.find_first with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{2} ");
      qv = q.find_last with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{2} ");

      qv = q.find with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_first with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_last with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");

      qi = q.find_index with (item == 2); qi.sort;
      v = $sformatf("%p", qi); `checks(v, "'{1, 2} ");
      qi = q.find_first_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{1} ");
      qi = q.find_last_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{2} ");

      qi = q.find_index with (item == 20); qi.sort;
      v = $sformatf("%p", qi); `checks(v, "'{}");
      qi = q.find_first_index with (item == 20);
      v = $sformatf("%p", qi); `checks(v, "'{}");
      qi = q.find_last_index with (item == 20);
      v = $sformatf("%p", qi); `checks(v, "'{}");

      qv = q.min;
      v = $sformatf("%p", qv); `checks(v, "'{1} ");
      qv = q.max;
      v = $sformatf("%p", qv); `checks(v, "'{4} ");

      // Reduction methods

      i = q.sum; `checkh(i, 32'hc);
      i = q.sum with (item + 1); `checkh(i, 32'h11);
      i = q.product; `checkh(i, 32'h30);
      i = q.product with (item + 1); `checkh(i, 32'h168);

      q = '{32'b1100, 32'b1010, 32'b1100, 32'b1010, 32'b1010};
      i = q.and; `checkh(i, 32'b1000);
      i = q.and with (item + 1); `checkh(i, 32'b1001);
      i = q.or; `checkh(i, 32'b1110);
      i = q.or with (item + 1); `checkh(i, 32'b1111);
      i = q.xor; `checkh(i, 32'ha);
      i = q.xor with (item + 1); `checkh(i, 32'hb);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
