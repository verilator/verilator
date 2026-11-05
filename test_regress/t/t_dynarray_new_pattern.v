// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  localparam int N = 3;

  int n = 4;
  int zero = 0;
  byte b = 8'h10;

  int decl[] = new[3] ('{1: 13, default: 14});

  class Base;
    int v;
    function new(int v);
      this.v = v;
    endfunction
  endclass
  class Sub extends Base;
    function new(int v);
      super.new(v);
    endfunction
  endclass

  initial begin
    automatic int ad[] = new[n] ('{default: 1});
    `checkh(ad.size, 4);
    `checkh(ad[0], 'h1);
    `checkh(ad[1], 'h1);
    `checkh(ad[2], 'h1);
    `checkh(ad[3], 'h1);

    `checkh(decl.size, 3);
    `checkh(decl[0], 'he);
    `checkh(decl[1], 'hd);
    `checkh(decl[2], 'he);

    begin  // new[size]('{index: value, default: value}), indices beyond the size are ignored
      localparam int K = 2;
      int a[];
      a = new[n] ('{12: 2, default: 3});
      `checkh(a.size, 4);
      `checkh(a[0], 'h3);
      `checkh(a[1], 'h3);
      `checkh(a[2], 'h3);
      `checkh(a[3], 'h3);
      a = new[n] ('{1: 5, 3: 6, 4: 7});
      `checkh(a.size, 4);
      `checkh(a[0], 'h0);
      `checkh(a[1], 'h5);
      `checkh(a[2], 'h0);
      `checkh(a[3], 'h6);
      a = new[N] ('{default: 9});
      `checkh(a.size, 3);
      `checkh(a[0], 'h9);
      `checkh(a[1], 'h9);
      `checkh(a[2], 'h9);
      a = new[zero] ('{0: 11, default: 12});
      `checkh(a.size, 0);
      a = new[n + 1] ('{2: n, default: n * 2});
      `checkh(a.size, 5);
      `checkh(a[0], 'h8);
      `checkh(a[1], 'h8);
      `checkh(a[2], 'h4);
      `checkh(a[3], 'h8);
      `checkh(a[4], 'h8);
      // Identifier keys
      a = new[3] ('{K: 4});
      `checkh(a.size, 3);
      `checkh(a[0], 'h0);
      `checkh(a[1], 'h0);
      `checkh(a[2], 'h4);
      // Keys alone, other elements have the default value of the type
      a = new[3] ('{2: 4});
      `checkh(a.size, 3);
      `checkh(a[0], 'h0);
      `checkh(a[1], 'h0);
      `checkh(a[2], 'h4);
      // Positional members only, the initializer is padded or truncated
      a = new[n] ('{1, 2});
      `checkh(a.size, 4);
      `checkh(a[0], 'h1);
      `checkh(a[1], 'h2);
      `checkh(a[2], 'h0);
      `checkh(a[3], 'h0);
      a = new[1] ('{1, 2});
      `checkh(a.size, 1);
      `checkh(a[0], 'h1);
    end

    begin  // The default applies to the elements of aggregate elements
      typedef struct {
        int x;
        byte y;
      } s_t;
      int ua[][2];
      s_t sta[];
      ua = new[2] ('{1: '{15, 16}, default: 17});
      `checkh(ua.size, 2);
      `checkh(ua[0][0], 17);
      `checkh(ua[0][1], 17);
      `checkh(ua[1][0], 15);
      `checkh(ua[1][1], 16);
      sta = new[2] ('{0: '{x: 18, y: 19}, default: 20});
      `checkh(sta.size, 2);
      `checkh(sta[0].x, 18);
      `checkh(sta[0].y, 19);
      `checkh(sta[1].x, 20);
      `checkh(sta[1].y, 20);
    end

    begin  // Element types
      bit [3:0] wstrb[];
      byte ba[];
      string sa[];
      logic [95:0] wa[];
      wstrb = new[N] ('{default: {32 / 8{1'b1}}});
      `checkh(wstrb.size, 3);
      `checkh(wstrb[0], 'hf);
      `checkh(wstrb[1], 'hf);
      `checkh(wstrb[2], 'hf);
      // Non-constant values whose expression is wider than the element
      ba = new[n] ('{1: b + 8'h1, default: b});
      `checkh(ba.size, 4);
      `checkh(ba[0], 'h10);
      `checkh(ba[1], 'h11);
      `checkh(ba[2], 'h10);
      `checkh(ba[3], 'h10);
      sa = new[N] ('{1: "one", default: "def"});
      `checkh(sa.size, 3);
      `checks(sa[0], "def");
      `checks(sa[1], "one");
      `checks(sa[2], "def");
      wa = new[N] ('{2: 96'h1_00000000_00000002, default: 96'hf_0000000e_0000000d});
      `checkh(wa.size, 3);
      `checkh(wa[0], 96'hf_0000000e_0000000d);
      `checkh(wa[1], 96'hf_0000000e_0000000d);
      `checkh(wa[2], 96'h1_00000000_00000002);
    end

    begin  // Values are truncated to the element width
      bit [3:0] c4;
      bit [3:0] q4[$];
      bit [3:0] d4[];
      c4 = 4'($urandom_range(15, 15));
      q4 = {c4 + 4'd2};
      `checkh(q4[0], 4'h1);
      d4 = new[2] ('{0: c4 + 4'd2, default: c4 + 4'd3});
      `checkh(d4[0], 4'h1);
      `checkh(d4[1], 4'h2);
    end

    begin  // Concatenation of values and arrays
      int q[$];
      int a[];
      byte bq[$];
      int fixed[2];
      q = {1, 2};
      q = {0, q, 3, q};
      `checkh(q.size, 6);
      `checkh(q[0], 'h0);
      `checkh(q[1], 'h1);
      `checkh(q[2], 'h2);
      `checkh(q[3], 'h3);
      `checkh(q[4], 'h1);
      `checkh(q[5], 'h2);
      a = {7, 8};
      a = {a[0], a, 6};
      `checkh(a.size, 4);
      `checkh(a[0], 'h7);
      `checkh(a[1], 'h7);
      `checkh(a[2], 'h8);
      `checkh(a[3], 'h6);
      bq = '{b + 8'h1};
      bq = {bq, b + 8'h2};
      `checkh(bq.size, 2);
      `checkh(bq[0], 'h11);
      `checkh(bq[1], 'h12);
      fixed = '{1, 2};
      a = {7, fixed, 8};
      `checkh(a.size, 4);
      `checkh(a[0], 'h7);
      `checkh(a[1], 'h1);
      `checkh(a[2], 'h2);
      `checkh(a[3], 'h8);
      q = {fixed, q};
      `checkh(q.size, 8);
      `checkh(q[0], 'h1);
      `checkh(q[1], 'h2);
      `checkh(q[2], 'h0);
      `checkh(q[3], 'h1);
      `checkh(q[4], 'h2);
      `checkh(q[5], 'h3);
      `checkh(q[6], 'h1);
      `checkh(q[7], 'h2);
    end

    begin  // IEEE 1800-2023 7.6
      string d[1:5];
      string p[];
      d = '{"a", "b", "c", "d", "e"};
      p = {d[1:3], "hello", d[4:5]};
      `checkh(p.size, 6);
      `checks(p[0], "a");
      `checks(p[1], "b");
      `checks(p[2], "c");
      `checks(p[3], "hello");
      `checks(p[4], "d");
      `checks(p[5], "e");
    end

    begin  // Arrays of arrays
      typedef int T_QI[$];
      T_QI jagged[$];
      int u[$][2];
      // IEEE 1800-2023 10.10.3
      jagged = '{{1}, T_QI'{2, 3, 4}, {5, 6}};
      `checkh(jagged[0].size, 1);
      `checkh(jagged[0][0], 'h1);
      `checkh(jagged[1].size, 3);
      `checkh(jagged[1][0], 'h2);
      `checkh(jagged[1][1], 'h3);
      `checkh(jagged[1][2], 'h4);
      `checkh(jagged[2].size, 2);
      `checkh(jagged[2][0], 'h5);
      `checkh(jagged[2][1], 'h6);
      // A queue is an element, a queue of queues is spliced
      jagged = {jagged, T_QI'{7}};
      `checkh(jagged[3].size, 1);
      `checkh(jagged[3][0], 'h7);
      jagged = {jagged, jagged};
      `checkh(jagged.size, 8);
      `checkh(jagged[7].size, 1);
      `checkh(jagged[7][0], 'h7);
      u = '{'{1, 2}, '{3, 4}};
      `checkh(u.size, 2);
      `checkh(u[0][0], 1);
      `checkh(u[0][1], 2);
      `checkh(u[1][0], 3);
      `checkh(u[1][1], 4);
    end

    begin  // A fixed-size array as an element of a queue of queues
      int fa[2];
      int qq[$][$];
      fa = '{1, 2};
      qq = '{fa};
      qq = {qq, fa};
      `checkh(qq.size, 2);
      `checkh(qq[1].size, 2);
      `checkh(qq[1][0], 1);
      `checkh(qq[1][1], 2);
    end

    begin  // Bounded queues
      typedef int T_B[$:1];
      int bounded[$:1];
      int q[$];
      // Elements beyond the bound are ignored
      bounded = {1, 2, 3};
      `checkh(bounded.size, 2);
      `checkh(bounded[0], 'h1);
      `checkh(bounded[1], 'h2);
      q = {T_B'{1, 2, 3}, 9};
      `checkh(q.size, 3);
      `checkh(q[0], 'h1);
      `checkh(q[1], 'h2);
      `checkh(q[2], 'h9);
      // Queues of a different bound
      q = {bounded, 9};
      `checkh(q.size, 3);
      `checkh(q[0], 'h1);
      `checkh(q[1], 'h2);
      `checkh(q[2], 'h9);
      bounded = {8, q};
      `checkh(bounded.size, 2);
      `checkh(bounded[0], 'h8);
      `checkh(bounded[1], 'h1);
    end

    begin  // Arrays to splice of another type
      typedef int T_QI[$];
      typedef byte T_QB[$];
      typedef byte T_DB[];
      int q[$];
      int a[];
      q = {T_QI'{}, 1};
      `checkh(q.size, 1);
      `checkh(q[0], 'h1);
      // Elements of another element type are converted
      // verilator lint_off WIDTHEXPAND
      q = {T_QB'{-8'sd1, 8'sd2}, 3};
      `checkh(q.size, 3);
      `checkh(q[0], 'hffffffff);
      `checkh(q[1], 'h2);
      `checkh(q[2], 'h3);
      // verilator lint_off WIDTHTRUNC
      q = {T_QB'{300}, 3};
      // verilator lint_on WIDTHTRUNC
      `checkh(q.size, 2);
      `checkh(q[0], 'h2c);
      `checkh(q[1], 'h3);
      // A dynamic array to splice into a queue, and the reverse
      q = {T_DB'{-8'sd1}, 5};
      `checkh(q.size, 2);
      `checkh(q[0], 'hffffffff);
      `checkh(q[1], 'h5);
      a = {T_QB'{-8'sd2}, T_QI'{7}};
      `checkh(a.size, 2);
      `checkh(a[0], 'hfffffffe);
      `checkh(a[1], 'h7);
      // verilator lint_on WIDTHEXPAND
    end

    begin  // Class handles
      Base cq[$];
      Sub sub;
      Sub sq[$];
      Sub suba[2];
      sub = new(21);
      // Converted to the element type, null is an element
      cq = {cq, sub, null};
      `checkh(cq.size, 2);
      `checkh(cq[0].v, 21);
      `checkh(cq[1] == null, 1'b1);
      // Queues and arrays of a derived class to splice
      sq = {sub};
      cq = {sub, sq};
      `checkh(cq.size, 2);
      `checkh(cq[1].v, 21);
      suba = '{sub, sub};
      cq = {cq, suba};
      `checkh(cq.size, 4);
      `checkh(cq[3].v, 21);
      // A fixed-size array of class handles as an element
      begin
        Base qa[$][$];
        qa = {suba};
        `checkh(qa.size, 1);
        `checkh(qa[0].size, 2);
        `checkh(qa[0][1].v, 21);
      end
      // A queue of a derived class as an element
      begin
        Base qq[$][$];
        qq = {qq, sq};
        `checkh(qq.size, 1);
        `checkh(qq[0].size, 1);
        `checkh(qq[0][0].v, 21);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
