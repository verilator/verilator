// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define check_rand(cl, field, cond) \
begin \
  automatic longint prev_result; \
  automatic int ok; \
  if (!bit'(cl.randomize())) $stop; \
  prev_result = longint'(field); \
  if (!(cond)) $stop; \
  repeat(9) begin \
    longint result; \
    if (!bit'(cl.randomize())) $stop; \
    result = longint'(field); \
    if (!(cond)) $stop; \
    if (result != prev_result) ok = 1; \
    prev_result = result; \
  end \
  if (ok != 1) $stop; \
end
`define check_rand_min_count(cl, field, exp_val, min_count) \
begin \
  automatic longint prev_result; \
  automatic int ok, count = 0; \
  if (!bit'(cl.randomize())) $stop; \
  prev_result = longint'(field); \
  if (field == exp_val) count++; \
  repeat(99) begin \
    longint result; \
    if (!bit'(cl.randomize())) $stop; \
    result = longint'(field); \
    if (field == exp_val) count++; \
    if (result != prev_result) ok = 1; \
    prev_result = result; \
  end \
  if (count < min_count) $stop; \
end
// verilog_format: on

class C;
  rand int x;
  int q[$] = {0, 0, 0, 0, 0};
  constraint fore {
    x < 7;
    foreach(q[i])
      x > i;
    foreach(q[i])  // loop again with the same index name
      x > i;
  };
endclass

class D;
  rand bit posit;
  rand int x;
  int o[$];  // empty
  int p[$] = {1};
  int q[$] = {0, 0, 0, 0, 0};
  constraint fore {
    if (posit == 1) {
      foreach(o[i]) o[i] > 0;
    }
    if (posit == 1) {
      foreach(p[i]) p[i] > 0;
    }
    if (posit == 1) {
      x < 7;
      foreach(q[i])
        x > i;
    } else {
      x > -3;
      foreach(q[i])
        x < i;
    }
  };
endclass

class E;
  typedef struct { rand bit [31:0]a; } cfg_t;
  rand cfg_t cfg[];

  function new();
    cfg = new [10];
  endfunction

  constraint e {
    foreach (cfg[i]) {
      // (i/2)*2 math is used to make sure we use i in array index and
      // not exceed table size
      solve cfg[(i/2)*2].a before cfg[(i/2)*2 + 1].a ;
      cfg[(i/2)*2 + 1].a != cfg[(i/2)*2].a;
    }
  }
endclass

class F;
  typedef struct { rand bit c; rand bit [7:0]d; }subcfg_t;
  typedef struct { subcfg_t subcfg[]; } cfg_t;
  rand cfg_t cfg[];
  rand bit b;

  function new();
    cfg = new [10];
    foreach (cfg[i]) begin
      cfg[i].subcfg = new [10];
    end
  endfunction

  constraint f {
    foreach (cfg[i]) {
      solve b before cfg[i].subcfg[0].d;
      cfg[i].subcfg[0].d[0] != b;
    }
  }
endclass

class G;
  typedef struct { rand bit [31:0]a; rand bit c; } cfg_t;
  rand cfg_t cfg[];
  rand bit b;

  function new();
    cfg = new [6];
  endfunction

  constraint g {
    foreach (cfg[i]) {
      solve b before cfg[i].a, cfg[i].c;

      b -> cfg[i].c == 1;
      b -> cfg[i].a == 0;
    }
  }
endclass

class H;
  rand integer a[];
  rand integer b;

  function new();
    a = new [6];
  endfunction

  constraint h {
    foreach (a[i]) {
      solve b before a[i];

      a[i] != b;
    }
  }
endclass

module t;
  initial begin
    automatic C c = new;
    automatic D d = new;
    automatic E e = new;
    automatic F f = new;
    automatic G g = new;
    automatic H h = new;

    `check_rand(c, c.x, 4 < c.x && c.x < 7);
    `check_rand(d, d.posit, (d.posit ? 4 : -3) < d.x && d.x < (d.posit ? 7 : 0));
    foreach (e.cfg[i]) begin
      `check_rand(e, e.cfg[i].a, (e.cfg[(i/2)*2].a != e.cfg[(i/2)*2 + 1].a));
    end
    foreach (f.cfg[i]) begin
      `check_rand(f, f.cfg[i].subcfg[0].d, (f.cfg[i].subcfg[0].d[0] != f.b));
    end
    foreach (g.cfg[i]) begin
      `check_rand_min_count(g, g.cfg[i].a, 0, 14);
    end
    foreach (h.a[i]) begin
      `check_rand(h, h.a[i], (h.a[i] != h.b));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
