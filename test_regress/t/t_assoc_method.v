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
      int qe[int];  // Empty
      int qv[$];  // Value returns
      int qi[$];  // Index returns
      int i;
      string v;

      q = '{10:1, 11:2, 12:2, 13:4, 14:3};
      v = $sformatf("%p", q); `checks(v, "'{'ha:'h1, 'hb:'h2, 'hc:'h2, 'hd:'h4, 'he:'h3} ");

      // NOT tested: with ... selectors

      //q.sort;  // Not legal on assoc - see t_assoc_meth_bad
      //q.rsort;  // Not legal on assoc - see t_assoc_meth_bad
      //q.reverse;  // Not legal on assoc - see t_assoc_meth_bad
      //q.shuffle;  // Not legal on assoc - see t_assoc_meth_bad

      v = $sformatf("%p", qe); `checks(v, "'{}");
      qv = q.unique;
      v = $sformatf("%p", qv); `checks(v, "'{'h1, 'h2, 'h4, 'h3} ");
      qv = qe.unique;
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qi = q.unique_index; qi.sort;
      v = $sformatf("%p", qi); `checks(v, "'{'ha, 'hb, 'hd, 'he} ");
      qi = qe.unique_index;
      v = $sformatf("%p", qi); `checks(v, "'{}");

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
      qv = q.find with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2, 'h2} ");
      qv = q.find_first with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2} ");
      qv = q.find_last with (item == 2);
      v = $sformatf("%p", qv); `checks(v, "'{'h2} ");

      qv = q.find with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_first with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");
      qv = q.find_last with (item == 20);
      v = $sformatf("%p", qv); `checks(v, "'{}");

      qi = q.find_index with (item == 2); qi.sort;
      v = $sformatf("%p", qi); `checks(v, "'{'hb, 'hc} ");
      qi = q.find_first_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'hb} ");
      qi = q.find_last_index with (item == 2);
      v = $sformatf("%p", qi); `checks(v, "'{'hc} ");

      qi = q.find_index with (item == 20); qi.sort;
      v = $sformatf("%p", qi); `checks(v, "'{}");
      qi = q.find_first_index with (item == 20);
      v = $sformatf("%p", qi); `checks(v, "'{}");
      qi = q.find_last_index with (item == 20);
      v = $sformatf("%p", qi); `checks(v, "'{}");

      qi = q.find_index with (item.index == 12);
      v = $sformatf("%p", qi); `checks(v, "'{'hc} ");
      qi = q.find with (item.index == 12);
      v = $sformatf("%p", qi); `checks(v, "'{'h2} ");

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
      i = q.product;
      `checkh(i, 32'h30);
      i = q.product with (item + 1);
      `checkh(i, 32'h168);

      i = qe.sum;
      `checkh(i, 32'h0);
      i = qe.product;
      `checkh(i, 32'h0);

      q = '{10:32'b1100, 11:32'b1010};
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

      i = q.and();
      `checkh(i, 32'b1000);
      i = q.and() with (item + 1);
      `checkh(i, 32'b1001);
      i = q.or();
      `checkh(i, 32'b1110);
      i = q.or() with (item + 1);
      `checkh(i, 32'b1111);
      i = q.xor();
      `checkh(i, 32'b0110);
      i = q.xor() with (item + 1);
      `checkh(i, 32'b0110);

      i = qe.and();
      `checkh(i, 32'b0);
      i = qe.or();
      `checkh(i, 32'b0);
      i = qe.xor();
      `checkh(i, 32'b0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
