// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      int q[$];
      int qe[$];  // Empty
      int qv[$];  // Value returns
      int qvunused[$];  // Value returns (unused)
      int qi[$];  // Index returns
      int i;
      string v;

      q = '{1, 2, 2, 4, 3};
      v = $sformatf("%p", q); `checks(v, "'{'h1, 'h2, 'h2, 'h4, 'h3} ");

      // sort/rsort with clause is the field to use for the sorting
      q.sort;
      v = $sformatf("%p", q); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      q.sort with (10 - item);
      v = $sformatf("%p", q); `checks(v, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      q.sort(x) with (10 - x);
      v = $sformatf("%p", q); `checks(v, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      qe.sort(x) with (10 - x);
      v = $sformatf("%p", qe); `checks(v, "'{}");
      q.rsort;
      v = $sformatf("%p", q); `checks(v, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      q.rsort with (10 - item);
      v = $sformatf("%p", q); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      qe.rsort(x) with (10 - x);
      v = $sformatf("%p", q); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");

      q = '{2, 2, 4, 1, 3};
      qv = q.unique;
      v = $sformatf("%p", qv); `checks(v, "'{'h2, 'h4, 'h1, 'h3} ");
      qv = qe.unique;
      `checkh(qv.size(), 0);
      qi = q.unique_index; qv.sort;
      v = $sformatf("%p", qi); `checks(v, "'{'h0, 'h2, 'h3, 'h4} ");
      qi = qe.unique_index;
      `checkh(qi.size(), 0);

      q.reverse;
      v = $sformatf("%p", q); `checks(v, "'{'h3, 'h1, 'h4, 'h2, 'h2} ");
      qe.reverse;
      `checkh(qe.size(), 0);
      q.shuffle(); q.sort;
      v = $sformatf("%p", q); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      qe.shuffle();
      `checkh(qe.size(), 0);

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
      qv = q.find with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2, 'h2} ");
      qv = q.find with (item[0] == 1);
      v = $sformatf("%p", qv); `checks(v, "'{'h1, 'h3} ");
      qv = q.find_first with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2} ");
      qv = q.find_last with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2} ");

      qv = q.find with (item == 20);
      `checkh(qv.size, 0);
      qv = q.find_first with (item == 20);
      `checkh(qv.size, 0);
      qv = q.find_last with (item == 20);
      `checkh(qv.size, 0);

      // Check gate eater with Lambda variable removal
      qvunused = q.find with (item == 20);

      qi = q.find_index with (item == 2);
      qi.sort; v = $sformatf("%p", qi); `checks(v, "'{'h1, 'h2} ");
      qi = q.find_first_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'h1} ");
      qi = q.find_last_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'h2} ");

      i = 2;
      qi = q.find_index with (item == i);
      qi.sort; v = $sformatf("%p", qi); `checks(v, "'{'h1, 'h2} ");

      qi = q.find_index with (item == 20); qi.sort;
      `checkh(qi.size, 0);
      qi = q.find_first_index with (item == 20);
      `checkh(qi.size, 0);
      qi = q.find_last_index with (item == 20);
      `checkh(qi.size, 0);

      qi = q.find_index with (item.index == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'h2} ");
      qi = q.find_index with (item.index == item);
      v = $sformatf("%p", qi); `checks(v, "'{'h2, 'h3, 'h4} ");

      qv = q.min;
      v = $sformatf("%p", qv); `checks(v, "'{'h1} ");
      qv = q.max;
      v = $sformatf("%p", qv); `checks(v, "'{'h4} ");
      qv = qe.min;
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = qe.max;
      v = $sformatf("%p", qv); `checks(v, "'{}");

      // Reduction methods
      i = q.sum;
      `checkh(i, 32'hc);
      i = q.sum with (item + 1);
      `checkh(i, 32'h11);
      i = q.sum(myi) with (myi + 1);
      `checkh(i, 32'h11);
      i = q.sum with (1);  // unused 'index'
      `checkh(i, 32'h5);
      i = q.sum(unused) with (1);  // unused 'unused'
      `checkh(i, 32'h5);

      i = q.product;
      `checkh(i, 32'h30);
      i = q.product with (item + 1);
      `checkh(i, 32'h168);

      i = qe.sum;
      `checkh(i, 32'h0);

      i = qe.product;
      `checkh(i, 32'h0);

      q = '{32'b1100, 32'b1010};
      i = q.and;
      `checkh(i, 32'b1000);
      i = q.and with (item + 1);
      `checkh(i, 32'b1001);
      i = q.or;
      `checkh(i, 32'b1110);
      i = q.or with (item + 1);
      `checkh(i, 32'b1111);
      i = q.xor;
      `checkh(i, 32'b0110);
      i = q.xor with (item + 1);
      `checkh(i, 32'b0110);

      i = qe.and;
      `checkh(i, 32'b0);
      i = qe.or;
      `checkh(i, 32'b0);
      i = qe.xor;
      `checkh(i, 32'b0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
