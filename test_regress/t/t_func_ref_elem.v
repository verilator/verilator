// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef bit [127:0] w_t;
typedef struct {
  int a;
  int sub[$];
} qs_t;
typedef struct {int aa[int];} as_t;
typedef int arr_t[2];

class Cls;
  int m[$];
  function void inc(ref int x);
    x++;
  endfunction
  function void winc(ref w_t x);
    x++;
  endfunction
  function int peek(const ref int x);
    return x;
  endfunction
  function bit aliased(ref w_t a, const ref w_t b);
    a++;
    return a == b;
  endfunction
  function int fwd_aa(const ref int a[int]);
    return peek(a[1]);
  endfunction
  function int fwd_q(const ref int a[$]);
    return peek(a[0]);
  endfunction
endclass

module t;
  int aa[int];
  int wc[*];
  w_t waa[int];
  w_t wq[$];
  qs_t qs[$];
  qs_t ds[];
  as_t qa[$];
  int qq[$][$];
  int qu[$][2];
  int uq[2][$];
  int aq[string][$];
  int wq2[*][$];
  int mem[4];
  qs_t ms;
  int y_mem, y_aa, y_ma, y_msub, idx;
  logic clk;

  function automatic int peek(const ref int x);
    return x;
  endfunction
  function automatic int get_v();
    return 3;
  endfunction
  function automatic arr_t get_arr();
    return '{4, 5};
  endfunction
  function automatic qs_t get_s();
    qs_t r;
    r.a = 6;
    return r;
  endfunction

  // A const ref only reads, so these blocks are sensitive to the argument and don't drive it
  always_comb y_mem = peek(mem[1]);
  always @* y_aa = peek(aa[2]);
  assign y_ma = peek(ms.a);
  assign y_msub = peek(ms.sub[0]);
  always_ff @(posedge clk) mem[idx] <= 1;

  initial begin
    automatic Cls c = new;
    automatic qs_t s;
    automatic as_t a;
    automatic int t[$] = '{6, 7};
    automatic int u[2] = '{6, 7};
    automatic int offset = -1;

    c.inc(aa[1]);
    `checkd(aa[1], 1);
    c.inc(wc[2]);
    `checkd(wc[2], 1);
    c.m.push_back(0);
    c.inc(c.m[0]);
    `checkd(c.m[0], 1);
    `checkd(c.peek(c.m[0]), 1);

    c.winc(waa[3]);
    `checkd(waa[3], 1);
    wq.push_back(0);
    c.winc(wq[0]);
    `checkd(wq[0], 1);
    `checkd(c.peek(aa[4]), 0);
    `checkd(aa.exists(4), 0);
    `checkd(c.aliased(waa[3], waa[3]), 1);
    `checkd(c.aliased(wq[0], wq[0]), 1);
    `checkd(c.aliased(wq[0], wq[$]), 1);
    `checkd(c.fwd_aa(aa), 1);
    `checkd(c.fwd_q(c.m), 1);

    s.sub = '{4, 5};
    qs.push_back(s);
    ds = new[1];
    ds[0] = s;
    qa.push_back(a);
    qq.push_back(t);
    qu.push_back(u);
    uq[1] = t;

    `checkd(c.peek(qs[0].sub[1]), 5);
    `checkd(c.peek(ds[0].sub[1]), 5);
    `checkd(c.peek(qa[0].aa[7]), 0);
    `checkd(qa[0].aa.exists(7), 0);
    `checkd(c.peek(qq[0][1]), 7);
    `checkd(c.peek(qu[0][1]), 7);
    `checkd(c.peek(uq[1][1]), 7);
    `checkd(c.peek(qu[$-offset][0]), 0);
    `checkd(qu.size(), 1);
    `checkd(c.peek(t[$-offset]), 0);
    `checkd(t.size(), 2);
    `checkd(c.peek(aq["k"][0]), 0);
    `checkd(aq.exists("k"), 0);
    `checkd(c.peek(wq2[3][0]), 0);
    `checkd(wq2.exists(3), 0);
    // A const ref only reads a function's returned value
    `checkd(peek(get_v()), 3);
    `checkd(peek(get_arr()[1]), 5);
    `checkd(peek(get_s().a), 6);

    // Checked in the final block, as the blocks above can only react once this block ends
    mem[1] = 5;
    aa[2] = 6;
    ms.a = 7;
    ms.sub.push_back(8);

    $write("*-* All Finished *-*\n");
    $finish;
  end

  final begin
    `checkd(y_mem, 5);
    `checkd(y_aa, 6);
    `checkd(y_ma, 7);
    `checkd(y_msub, 8);
  end
endmodule
