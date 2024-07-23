// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) !== (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

module t (/*AUTOARG*/);
   typedef struct { int x, y; } point;
   initial begin
      int q[int];
      int qe[int];  // Empty
      int qv[$];  // Value returns
      int qi[$];  // Index returns
      point points_q[int];
      point points_qv[$];
      int i;

      q = '{10:1, 11:2, 12:2, 13:4, 14:3};
      `checkp(q, "'{'ha:'h1, 'hb:'h2, 'hc:'h2, 'hd:'h4, 'he:'h3} ");

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
      qi = q.unique_index; qi.sort;
      `checkp(qi, "'{'ha, 'hb, 'hd, 'he} ");
      qi = qe.unique_index;
      `checkp(qi, "'{}");

      points_q[0] = point'{1, 2};
      points_q[1] = point'{2, 4};
      points_q[5] = point'{1, 4};

      points_qv = points_q.unique(p) with (p.x);
      `checkh(points_qv.size, 2);
      qi = points_q.unique_index(p) with (p.x + p.y);
      qi.sort;
      `checkp(qi, "'{'h0, 'h1, 'h5} ");

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
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

      qi = q.find_index with (item == 2); qi.sort;
      `checkp(qi, "'{'hb, 'hc} ");
      qi = q.find_first_index with (item == 2);
      `checkp(qi, "'{'hb} ");
      qi = q.find_last_index with (item == 2);
      `checkp(qi, "'{'hc} ");

      qi = q.find_index with (item == 20); qi.sort;
      `checkp(qi, "'{}");
      qi = q.find_first_index with (item == 20);
      `checkp(qi, "'{}");
      qi = q.find_last_index with (item == 20);
      `checkp(qi, "'{}");

      qi = q.find_index with (item.index == 12);
      `checkp(qi, "'{'hc} ");
      qi = q.find with (item.index == 12);
      `checkp(qi, "'{'h2} ");

      qv = q.min;
      `checkp(qv, "'{'h1} ");
      points_qv = points_q.min(p) with (p.x + p.y);
      if (points_qv[0].x != 1 || points_qv[0].y != 2) $stop;

      qv = q.max;
      `checkp(qv, "'{'h4} ");
      points_qv = points_q.max(p) with (p.x + p.y);
      if (points_qv[0].x != 2 || points_qv[0].y != 4) $stop;

      qv = qe.min;
      `checkp(qv, "'{}");
      qv = qe.min(x) with (x + 1);
      `checkp(qv, "'{}");
      qv = qe.max;
      `checkp(qv, "'{}");
      qv = qe.max(x) with (x + 1);
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

      q = '{10:1, 11:2};
      qe = '{10:1, 11:2};
      `checkh(q == qe, 1'b1);
      `checkh(q != qe, 1'b0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
