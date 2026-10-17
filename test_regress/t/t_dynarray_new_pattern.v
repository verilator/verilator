// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
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
    `checkp(ad, "'{'h1, 'h1, 'h1, 'h1}");

    `checkp(decl, "'{'he, 'hd, 'he}");

    begin  // new[size]('{index: value, default: value}), indices out of bounds are ignored
      localparam int K = 2;
      int a[];
      a = new[n] ('{12: 2, default: 3});
      `checkp(a, "'{'h3, 'h3, 'h3, 'h3}");
      a = new[n] ('{1: 5, 3: 6, 4: 7, -1: 8});
      `checkp(a, "'{'h0, 'h5, 'h0, 'h6}");
      a = new[N] ('{default: 9});
      `checkp(a, "'{'h9, 'h9, 'h9}");
      a = new[zero] ('{0: 11, default: 12});
      `checkp(a, "'{}");
      a = new[n + 1] ('{2: n, default: n * 2});
      `checkp(a, "'{'h8, 'h8, 'h4, 'h8, 'h8}");
      // Identifier keys
      a = new[3] ('{K: 4});
      `checkp(a, "'{'h0, 'h0, 'h4}");
      // Indices wider than 32 bits are out of bounds, not truncated
      a = new[3] ('{64'h1_0000_0001: 5, 1: 6});
      `checkp(a, "'{'h0, 'h6, 'h0}");
      // Keys alone, other elements have the default value of the type
      a = new[3] ('{2: 4});
      `checkp(a, "'{'h0, 'h0, 'h4}");
      // Positional members only, the initializer is padded or truncated
      a = new[n] ('{1, 2});
      `checkp(a, "'{'h1, 'h2, 'h0, 'h0}");
      a = new[1] ('{1, 2});
      `checkp(a, "'{'h1}");
    end

    begin  // The default applies to the elements of aggregate elements
      typedef struct {
        int x;
        byte y;
      } s_t;
      int ua[][2];
      s_t sta[];
      ua = new[2] ('{1: '{15, 16}, default: 17});
      if (ua.size != 2 || ua[0][0] != 17 || ua[0][1] != 17 || ua[1][0] != 15 || ua[1][1] != 16)
        `stop;
      sta = new[2] ('{0: '{x: 18, y: 19}, default: 20});
      if (sta.size != 2 || sta[0].x != 18 || sta[0].y != 19 || sta[1].x != 20 || sta[1].y != 20)
        `stop;
    end

    begin  // Element types
      bit [3:0] wstrb[];
      byte ba[];
      string sa[];
      logic [95:0] wa[];
      wstrb = new[N] ('{default: {32 / 8{1'b1}}});
      `checkp(wstrb, "'{'hf, 'hf, 'hf}");
      // Non-constant values whose expression is wider than the element
      ba = new[n] ('{1: b + 8'h1, default: b});
      `checkp(ba, "'{'h10, 'h11, 'h10, 'h10}");
      sa = new[N] ('{1: "one", default: "def"});
      `checkp(sa, "'{\"def\", \"one\", \"def\"}");
      wa = new[N] ('{2: 96'h1_00000000_00000002, default: 96'hf_0000000e_0000000d});
      if (wa.size != 3 || wa[0] != 96'hf_0000000e_0000000d || wa[1] != 96'hf_0000000e_0000000d
          || wa[2] != 96'h1_00000000_00000002) `stop;
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
      `checkp(q, "'{'h0, 'h1, 'h2, 'h3, 'h1, 'h2}");
      a = {7, 8};
      a = {a[0], a, 6};
      `checkp(a, "'{'h7, 'h7, 'h8, 'h6}");
      bq = '{b + 8'h1};
      bq = {bq, b + 8'h2};
      `checkp(bq, "'{'h11, 'h12}");
      fixed = '{1, 2};
      a = {7, fixed, 8};
      `checkp(a, "'{'h7, 'h1, 'h2, 'h8}");
      q = {fixed, q};
      `checkp(q, "'{'h1, 'h2, 'h0, 'h1, 'h2, 'h3, 'h1, 'h2}");
    end

    begin  // IEEE 1800-2023 7.6
      string d[1:5];
      string p[];
      d = '{"a", "b", "c", "d", "e"};
      p = {d[1:3], "hello", d[4:5]};
      `checkp(p, "'{\"a\", \"b\", \"c\", \"hello\", \"d\", \"e\"}");
    end

    begin  // Arrays of arrays
      typedef int T_QI[$];
      T_QI jagged[$];
      int u[$][2];
      // IEEE 1800-2023 10.10.3
      jagged = '{{1}, T_QI'{2, 3, 4}, {5, 6}};
      `checkp(jagged[0], "'{'h1}");
      `checkp(jagged[1], "'{'h2, 'h3, 'h4}");
      `checkp(jagged[2], "'{'h5, 'h6}");
      // A queue is an element, a queue of queues is spliced
      jagged = {jagged, T_QI'{7}};
      `checkp(jagged[3], "'{'h7}");
      jagged = {jagged, jagged};
      if (jagged.size != 8) `stop;
      `checkp(jagged[7], "'{'h7}");
      u = '{'{1, 2}, '{3, 4}};
      if (u.size != 2 || u[0][0] != 1 || u[0][1] != 2 || u[1][0] != 3 || u[1][1] != 4) `stop;
    end

    begin  // A fixed-size array as an element of a queue of queues
      int fa[2];
      int qq[$][$];
      fa = '{1, 2};
      qq = '{fa};
      qq = {qq, fa};
      if (qq.size != 2 || qq[1].size != 2 || qq[1][0] != 1 || qq[1][1] != 2) `stop;
    end

    begin  // Bounded queues
      typedef int T_B[$:1];
      int bounded[$:1];
      int q[$];
      // Elements beyond the bound are ignored
      bounded = {1, 2, 3};
      `checkp(bounded, "'{'h1, 'h2}");
      q = {T_B'{1, 2, 3}, 9};
      `checkp(q, "'{'h1, 'h2, 'h9}");
      // Queues of a different bound
      q = {bounded, 9};
      `checkp(q, "'{'h1, 'h2, 'h9}");
      bounded = {8, q};
      `checkp(bounded, "'{'h8, 'h1}");
    end

    begin  // Arrays to splice of another type
      typedef int T_QI[$];
      typedef byte T_QB[$];
      typedef byte T_DB[];
      int q[$];
      int a[];
      q = {T_QI'{}, 1};
      `checkp(q, "'{'h1}");
      // Elements of another element type are converted
      // verilator lint_off WIDTHEXPAND
      q = {T_QB'{-8'sd1, 8'sd2}, 3};
      `checkp(q, "'{'hffffffff, 'h2, 'h3}");
      // verilator lint_off WIDTHTRUNC
      q = {T_QB'{300}, 3};
      // verilator lint_on WIDTHTRUNC
      `checkp(q, "'{'h2c, 'h3}");
      // A dynamic array to splice into a queue, and the reverse
      q = {T_DB'{-8'sd1}, 5};
      `checkp(q, "'{'hffffffff, 'h5}");
      a = {T_QB'{-8'sd2}, T_QI'{7}};
      `checkp(a, "'{'hfffffffe, 'h7}");
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
      if (cq.size != 2 || cq[0].v != 21 || cq[1] != null) `stop;
      // Queues and arrays of a derived class to splice
      sq = {sub};
      cq = {sub, sq};
      if (cq.size != 2 || cq[1].v != 21) `stop;
      suba = '{sub, sub};
      cq = {cq, suba};
      if (cq.size != 4 || cq[3].v != 21) `stop;
      // A fixed-size array of class handles as an element
      begin
        Base qa[$][$];
        qa = {suba};
        if (qa.size != 1 || qa[0].size != 2 || qa[0][1].v != 21) `stop;
      end
      // A queue of a derived class as an element
      begin
        Base qq[$][$];
        qq = {qq, sq};
        if (qq.size != 1 || qq[0].size != 1 || qq[0][0].v != 21) `stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
