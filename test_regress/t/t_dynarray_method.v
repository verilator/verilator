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

   string s[] = { "hello", "sad", "sad", "world" };

   initial begin
      int d[];
      int de[];  // Empty
      int qv[$];  // Value returns
      int qvunused[$];  // Value returns (unused)
      int qi[$];  // Index returns
      int i;
      string v;

      d = '{1, 2, 2, 4, 3};
      v = $sformatf("%p", d); `checks(v, "'{'h1, 'h2, 'h2, 'h4, 'h3} ");
      d = {1, 2, 2, 4, 3};
      v = $sformatf("%p", d); `checks(v, "'{'h1, 'h2, 'h2, 'h4, 'h3} ");

      // sort/rsort with clause is the field to use for the sorting
      d.sort;
      v = $sformatf("%p", d); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      d.sort with (10 - item);
      v = $sformatf("%p", d); `checks(v, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      d.sort(x) with (10 - x);
      v = $sformatf("%p", d); `checks(v, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      de.sort(x) with (10 - x);
      v = $sformatf("%p", de); `checks(v, "'{}");
      d.rsort;
      v = $sformatf("%p", d); `checks(v, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      d.rsort with (10 - item);
      v = $sformatf("%p", d); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      de.rsort(x) with (10 - x);
      v = $sformatf("%p", d); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");

      d = '{2, 2, 4, 1, 3};
      qv = d.unique;
      v = $sformatf("%p", qv); `checks(v, "'{'h2, 'h4, 'h1, 'h3} ");
      qv = de.unique;
      `checkh(qv.size(), 0);
      qi = d.unique_index; qv.sort;
      v = $sformatf("%p", qi); `checks(v, "'{'h0, 'h2, 'h3, 'h4} ");
      qi = de.unique_index;
      `checkh(qi.size(), 0);

      d.reverse;
      v = $sformatf("%p", d); `checks(v, "'{'h3, 'h1, 'h4, 'h2, 'h2} ");
      de.reverse;
      `checkh(de.size(), 0);
      d.shuffle(); d.sort;
      v = $sformatf("%p", d); `checks(v, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      de.shuffle();
      `checkh(de.size(), 0);

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
      qv = d.find with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2, 'h2} ");
      qv = d.find_first with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2} ");
      qv = d.find_last with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2} ");

      qv = d.find with (item == 20);
      `checkh(qv.size, 0);
      qv = d.find_first with (item == 20);
      `checkh(qv.size, 0);
      qv = d.find_last with (item == 20);
      `checkh(qv.size, 0);

      // Check gate eater with Lambda variable removal
      qvunused = d.find with (item == 20);

      qi = d.find_index with (item == 2);
      qi.sort; v = $sformatf("%p", qi); `checks(v, "'{'h1, 'h2} ");
      qi = d.find_first_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'h1} ");
      qi = d.find_last_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'h2} ");

      i = 2;
      qi = d.find_index with (item == i);
      qi.sort; v = $sformatf("%p", qi); `checks(v, "'{'h1, 'h2} ");

      qi = d.find_index with (item == 20); qi.sort;
      `checkh(qi.size, 0);
      qi = d.find_first_index with (item == 20);
      `checkh(qi.size, 0);
      qi = d.find_last_index with (item == 20);
      `checkh(qi.size, 0);

      qi = d.find_index with (item.index == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'h2} ");

      qv = d.min;
      v = $sformatf("%p", qv); `checks(v, "'{'h1} ");
      qv = d.max;
      v = $sformatf("%p", qv); `checks(v, "'{'h4} ");
      qv = de.min;
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = de.max;
      v = $sformatf("%p", qv); `checks(v, "'{}");

      // Reduction methods
      i = d.sum;
      `checkh(i, 32'hc);
      i = d.sum with (item + 1);
      `checkh(i, 32'h11);
      i = d.sum(myi) with (myi + 1);
      `checkh(i, 32'h11);
      i = d.sum with (1);  // unused 'index'
      `checkh(i, 32'h5);
      i = d.sum(unused) with (1);  // unused 'unused'
      `checkh(i, 32'h5);

      i = d.product;
      `checkh(i, 32'h30);
      i = d.product with (item + 1);
      `checkh(i, 32'h168);

      i = de.sum;
      `checkh(i, 32'h0);

      i = de.product;
      `checkh(i, 32'h0);

      d = '{32'b1100, 32'b1010};

      i = d.and;
      `checkh(i, 32'b1000);
      i = d.and with (item + 1);
      `checkh(i, 32'b1001);
      i = d.or;
      `checkh(i, 32'b1110);
      i = d.or with (item + 1);
      `checkh(i, 32'b1111);
      i = d.xor;
      `checkh(i, 32'b0110);
      i = d.xor with (item + 1);
      `checkh(i, 32'b0110);

      i = de.and;
      `checkh(i, 32'b0);
      i = de.or;
      `checkh(i, 32'b0);
      i = de.xor;
      `checkh(i, 32'b0);

      `checks(s[1], "sad");
      qi = s.find_first_index with (item == "sad");
      `checkh(qi.size, 1);
      `checkh(qi[0], 1);
      qi = s.find_last_index with (item == "sad");
      `checkh(qi.size, 1);
      `checkh(qi[0], 2);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
