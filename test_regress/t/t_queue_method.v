// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) !== (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

class Cls;
   int x;
   function new(int a);
      x = a;
   endfunction
endclass

module t (/*AUTOARG*/);
   typedef struct packed { int x, y; } point;
   typedef struct packed { point p; int z; } point_3d;
   initial begin
      int q[$];
      int qe[$];  // Empty
      int qv[$];  // Value returns
      int qvunused[$];  // Value returns (unused)
      int qi[$];  // Index returns
      int i;
      bit b;
      string string_q[$];
      string string_qv[$];
      point_3d points_q[$];  // Same as q and qv, but complex value type
      point_3d points_qv[$];
      Cls cls;
      Cls cls_q[$];
      Cls cls_qv[$];

      points_q.push_back(point_3d'{point'{1, 2}, 3});
      points_q.push_back(point_3d'{point'{2, 3}, 5});
      points_q.push_back(point_3d'{point'{1, 4}, 5});


      cls = new(1);
      cls_q.push_back(cls);
      cls = new(2);
      cls_q.push_back(cls);
      cls = new(1);
      cls_q.push_back(cls);

      string_q.push_back("a");
      string_q.push_back("A");
      string_q.push_back("b");

      q = '{1, 2, 2, 4, 3};
      `checkp(q, "'{'h1, 'h2, 'h2, 'h4, 'h3} ");

      // sort/rsort with clause is the field to use for the sorting
      q.sort;
      `checkp(q, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      q.sort with (10 - item);
      `checkp(q, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      q.sort(x) with (10 - x);
      `checkp(q, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      qe.sort(x) with (10 - x);
      `checkp(qe, "'{}");
      q.rsort;
      `checkp(q, "'{'h4, 'h3, 'h2, 'h2, 'h1} ");
      q.rsort with (10 - item);
      `checkp(q, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      qe.rsort(x) with (10 - x);
      `checkp(q, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");

      q = '{2, 2, 4, 1, 3};
      qv = q.unique;
      `checkp(qv, "'{'h2, 'h4, 'h1, 'h3} ");
      qv = qe.unique;
      `checkh(qv.size(), 0);
      qv = q.unique(x) with (x % 2);
      `checkh(qv.size(), 2);
      string_qv = string_q.unique(s) with (s.toupper);
      `checkh(string_qv.size(), 2);
      qi = q.unique_index; qv.sort;
      // According to IEEE 1800-2023 7.12.1, it is not specified which index of duplicated value should be returned
      `checkh(qi.size(), 4);
      qi.delete(1);
      `checkp(qi, "'{'h0, 'h3, 'h4} ");
      qi = qe.unique_index;
      `checkh(qi.size(), 0);
      qi = q.unique_index(x) with (x % 3); qv.sort;
      `checkh(qi.size(), 3);
      cls_qv = cls_q.unique with (item.x);
      `checkh(cls_qv.size(), 2);
      cls_qv = cls_q.unique with (item.x < 10);
      `checkh(cls_qv.size(), 1);
      qi = cls_q.unique_index with (item.x % 2);
      qi.sort;
      `checkp(qi, "'{'h0, 'h1} ");

      q.reverse;
      `checkp(q, "'{'h3, 'h1, 'h4, 'h2, 'h2} ");
      qe.reverse;
      `checkh(qe.size(), 0);
      q.shuffle(); q.sort;
      `checkp(q, "'{'h1, 'h2, 'h2, 'h3, 'h4} ");
      qe.shuffle();
      `checkh(qe.size(), 0);

      // These require an with clause or are illegal
      // TODO add a lint check that with clause is provided
      qv = q.find with (item == 2);
      `checkp(qv, "'{'h2, 'h2} ");
      qv = q.find with (item[0] == 1);
      `checkp(qv, "'{'h1, 'h3} ");
      qv = q.find_first with (item == 2);
      `checkp(qv, "'{'h2} ");
      points_qv = points_q.find_first with (item.z == 5);
      `checkh(points_qv[0].p.y, 3);
      points_qv = points_q.find_first with (item.p.x == 1);
      `checkh(points_qv[0].p.y, 2);
      qv = q.find_last with (item == 2);
      `checkp(qv, "'{'h2} ");
      string_qv = string_q.find_last(s) with (s.tolower() == "a");
      `checks(string_qv[0], "A");

      qv = q.find with (item == 20);
      `checkh(qv.size, 0);
      qv = q.find_first with (item == 20);
      `checkh(qv.size, 0);
      qv = q.find_last with (item == 20);
      `checkh(qv.size, 0);

      // Check gate eater with Lambda variable removal
      qvunused = q.find with (item == 20);

      qi = q.find_index with (item == 2);
      qi.sort; `checkp(qi, "'{'h1, 'h2} ");
      qi = q.find_first_index with (item == 2);
      `checkp(qi, "'{'h1} ");
      qi = q.find_last_index with (item == 2);
      `checkp(qi, "'{'h2} ");

      i = 2;
      qi = q.find_index with (item == i);
      qi.sort; `checkp(qi, "'{'h1, 'h2} ");

      qi = q.find_index with (item == 20); qi.sort;
      `checkh(qi.size, 0);
      qi = q.find_first_index with (item == 20);
      `checkh(qi.size, 0);
      qi = q.find_last_index with (item == 20);
      `checkh(qi.size, 0);

      qi = q.find_index with (item.index == 2);
      `checkp(qi, "'{'h2} ");
      qi = q.find_index with (item.index == item);
      `checkp(qi, "'{'h2, 'h3, 'h4} ");

      qv = q.min;
      `checkp(qv, "'{'h1} ");
      qv = q.min(x) with (x + 1);
      `checkp(qv, "'{'h1} ");
      qv = q.max;
      `checkp(qv, "'{'h4} ");
      qv = q.max(x) with ((x % 4) + 100);
      `checkp(qv, "'{'h3} ");
      qv = qe.min;
      `checkp(qv, "'{}");
      qv = qe.max;
      `checkp(qv, "'{}");

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
      i = qe.sum with (item + 1);
      `checkh(i, 32'h0);

      i = qe.product;
      `checkh(i, 32'h1);
      i = qe.product with (item + 1);
      `checkh(i, 32'h1);

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
      `checkh(i, 32'hffff_ffff);
      i = qe.and with (item + 1);
      `checkh(i, 32'hffff_ffff);
      i = qe.or;
      `checkh(i, 32'b0);
      i = qe.or with (item + 1);
      `checkh(i, 32'b0);
      i = qe.xor;
      `checkh(i, 32'b0);
      i = qe.xor with (item + 1);
      `checkh(i, 32'b0);

      q = '{1, 2};
      qe = '{1, 2};
      `checkh(q == qe, 1'b1);
      `checkh(q != qe, 1'b0);

      string_q = {"a", "bc", "def", "ghij"};

      i = string_q.sum with (item.len);
      `checkh(i, 10);
      i = string_q.product with (item.len);
      `checkh(i, 24);
      b = string_q.sum with (item == "bc");
      `checkh(b, 1'b1);
      b = string_q.sum with (item == "");
      `checkh(b, 1'b0);
      b = string_q.product with (item inside {"a", "bc", "def"});
      `checkh(b, 1'b0);
      b = string_q.product with (item inside {"a", "bc", "def", "ghij"});
      `checkh(b, 1'b1);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
