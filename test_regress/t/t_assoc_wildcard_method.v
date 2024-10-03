// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) !== (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

module t (/*AUTOARG*/);
   initial begin
      int q[*];
      int qe [ * ];  // Empty - Note spaces around [*] for parsing coverage
      int qv[$];  // Value returns
      int qi[$];  // Index returns
      int i;
      string v;

      q = '{"a":1, "b":2, "c":2, "d":4, "e":3};
      `checkp(q, "'{\"a\":'h1, \"b\":'h2, \"c\":'h2, \"d\":'h4, \"e\":'h3} ");

      // NOT tested: with ... selectors

      //q.sort;  // Not legal on assoc - see t_assoc_meth_bad
      //q.rsort;  // Not legal on assoc - see t_assoc_meth_bad
      //q.reverse;  // Not legal on assoc - see t_assoc_meth_bad
      //q.shuffle;  // Not legal on assoc - see t_assoc_meth_bad

      `checkp(qe, "'{}");
      qv = q.unique;
      `checkp(qv, "'{'h1, 'h2, 'h4, 'h3} ");
      qv = qe.unique;
      `checkp(qv, "'{}");

      //q.unique_index;  // Not legal on wildcard assoc - see t_assoc_wildcard_bad

      // These require an with clause or are illegal
      qv = q.find with (item == 2);
      `checkp(qv, "'{'h2, 'h2} ");
      qv = q.find_first with (item == 2);
      `checkp(qv, "'{'h2} ");
      qv = q.find_last with (item == 2);
      `checkp(qv, "'{'h2} ");

      qv = q.find with (item == 20);
      `checkp(qv, "'{}");
      qv = q.find_first with (item == 20);
      `checkp(qv, "'{}");
      qv = q.find_last with (item == 20);
      `checkp(qv, "'{}");

      //q.find_index;  // Not legal on wildcard assoc - see t_assoc_wildcard_bad
      //q.find_first_index;  // Not legal on wildcard assoc - see t_assoc_wildcard_bad
      //q.find_last_index;  // Not legal on wildcard assoc - see t_assoc_wildcard_bad

      qv = q.min;
      `checkp(qv, "'{'h1} ");
      qv = q.max;
      `checkp(qv, "'{'h4} ");

      qv = qe.min;
      `checkp(qv, "'{}");
      qv = qe.max;
      `checkp(qv, "'{}");

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
