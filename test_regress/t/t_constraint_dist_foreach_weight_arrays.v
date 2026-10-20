// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test dist constraints whose weights depend on the loop index and on other random
// variables, over several arrays inside one foreach. The weights must use the solved
// values of those variables, not their values from before randomize().
// The array variants give P(0) = 1/2 on "edge" elements (i < first || i >= n - last)
// and P(0) = 1/4 on "inner" elements, so the same checker applies to all of them.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

`define IS_EDGE(i, obj) ((i) < (obj).first || (i) >= (obj).n - (obj).last)

class Stats;
  string name;
  int edge_zero, edge_total, inner_zero, inner_total;
  function new(string name);
    this.name = name;
  endfunction
  function void add(bit is_edge, bit is_zero);
    if (is_edge) begin
      edge_total++;
      if (is_zero) edge_zero++;
    end
    else begin
      inner_total++;
      if (is_zero) inner_zero++;
    end
  endfunction
  function void check();
    int edge_pct, inner_pct;
    if (edge_total < 100 || inner_total < 100) begin
      $write("%%Error: %s: too few samples (edge=%0d inner=%0d)\n", name, edge_total, inner_total);
      `stop;
    end
    edge_pct = edge_zero * 100 / edge_total;
    inner_pct = inner_zero * 100 / inner_total;
`ifdef TEST_VERBOSE
    $display("%s: edge P(0)=%0d%% (%0d)  inner P(0)=%0d%% (%0d)", name, edge_pct, edge_total,
             inner_pct, inner_total);
`endif
    `check_range(edge_pct, 38, 62);
    `check_range(inner_pct, 13, 37);
  endfunction
endclass

// Two dynamic arrays, :/ weights computed from the index and other rand vars
class ClsDynDyn;
  rand int unsigned n, first, last;
  rand bit [1:0] a[];
  rand bit [1:0] b[];
  constraint c {
    a.size() == n;
    b.size() == n;
    n inside {[2:8]};
    first inside {[1:n]};
    last inside {[1:n]};
    foreach (a[i]) {
      a[i] dist {
        0 :/ ((i < first || i >= n - last) ? 50 : 25),
        [1:3] :/ ((i < first || i >= n - last) ? 50 : 75)
      };
      b[i] dist {
        0 :/ ((i < first || i >= n - last) ? 50 : 25),
        [1:3] :/ ((i < first || i >= n - last) ? 50 : 75)
      };
    }
  }
endclass

// Dynamic array plus queue, := weights (per value)
class ClsDynQueue;
  rand int unsigned n, first, last;
  rand bit [1:0] a[];
  rand bit [1:0] b[$];
  constraint c {
    a.size() == n;
    b.size() == n;
    n inside {[2:8]};
    first inside {[1:n]};
    last inside {[1:n]};
    foreach (a[i]) {
      a[i] dist {
        0 := ((i < first || i >= n - last) ? 3 : 1),
        [1:3] := 1
      };
      b[i] dist {
        0 := ((i < first || i >= n - last) ? 3 : 1),
        [1:3] := 1
      };
    }
  }
endclass

// Three arrays, weights from non-rand members, wider element type
class ClsThree;
  rand int unsigned n, first, last;
  rand bit [3:0] a[];
  rand bit [3:0] b[];
  rand bit [3:0] c[];
  int edge_w = 50;
  int inner_w = 25;
  constraint c_sz {
    a.size() == n;
    b.size() == n;
    c.size() == n;
    n inside {[2:8]};
    first inside {[1:n]};
    last inside {[1:n]};
  }
  constraint c_dist {
    foreach (a[i]) {
      a[i] dist {
        0 :/ ((i < first || i >= n - last) ? edge_w : inner_w),
        [1:15] :/ ((i < first || i >= n - last) ? 100 - edge_w : 100 - inner_w)
      };
      b[i] dist {
        0 :/ ((i < first || i >= n - last) ? edge_w : inner_w),
        [1:15] :/ ((i < first || i >= n - last) ? 100 - edge_w : 100 - inner_w)
      };
      c[i] dist {
        0 :/ ((i < first || i >= n - last) ? edge_w : inner_w),
        [1:15] :/ ((i < first || i >= n - last) ? 100 - edge_w : 100 - inner_w)
      };
    }
  }
endclass

// Same weights, but the variables they depend on are not random
class ClsFixed;
  int unsigned n = 6, first = 2, last = 2;
  rand bit [1:0] a[];
  rand bit [1:0] b[];
  constraint c {
    a.size() == n;
    b.size() == n;
    foreach (a[i]) {
      a[i] dist {
        0 :/ ((i < first || i >= n - last) ? 50 : 25),
        [1:3] :/ ((i < first || i >= n - last) ? 50 : 75)
      };
      b[i] dist {
        0 :/ ((i < first || i >= n - last) ? 50 : 25),
        [1:3] :/ ((i < first || i >= n - last) ? 50 : 75)
      };
    }
  }
endclass

// Fixed-size array: no resize pass, weights still depend on rand vars
class ClsUnpacked;
  rand int unsigned n, first, last;
  rand bit [1:0] a[8];
  constraint c {
    n == 8;
    first inside {[1:3]};
    last inside {[1:3]};
    foreach (a[i]) {
      a[i] dist {
        0 :/ ((i < first || i >= n - last) ? 50 : 25),
        [1:3] :/ ((i < first || i >= n - last) ? 50 : 75)
      };
    }
  }
endclass

// Total weight depends on a rand var k: P(x == 0) = k / (k + 1). The variants
// differ in how k is declared and whether anything else constrains it.
typedef enum bit [1:0] {
  E0 = 0,
  E1 = 1,
  E2 = 2,
  E3 = 3
} e_t;
typedef struct packed {
  bit [1:0] w;
  bit [1:0] pad;
} s_t;

class ClsTotal;
  rand bit [3:0] k;
  rand bit x;
  constraint c {
    k inside {[1:3]};
    x dist {0 := k, 1 := 1};
  }
endclass

// k is read only by the weight, so no other constraint mentions it
class ClsWeightOnly;
  rand bit [1:0] k;
  rand bit x;
  constraint c {x dist {0 := k, 1 := 1};}
endclass

class ClsEnum;
  rand e_t k;
  rand bit x;
  constraint c {
    k != E0;
    x dist {0 := k, 1 := 1};
  }
endclass

class ClsStatic;
  static rand bit [1:0] k;
  rand bit x;
  constraint c {
    k != 0;
    x dist {0 := k, 1 := 1};
  }
endclass

class ClsStruct;
  rand s_t s;
  rand bit x;
  constraint c {
    s.w != 0;
    x dist {0 := s.w, 1 := 1};
  }
endclass

class ClsBase;
  rand bit [1:0] k;
  constraint c_base {k != 0;}
endclass

class ClsDerived extends ClsBase;
  rand bit x;
  constraint c {x dist {0 := k, 1 := 1};}
endclass

// Weights reading vars that cannot be pinned (wider than 64 bits, or through a
// rand object handle) keep their old handling; only check they still solve
class ClsInner;
  rand bit [1:0] w;
  constraint c_inner {w != 0;}
endclass

class ClsNotPinned;
  rand bit [64:0] big;
  rand ClsInner inner;
  rand bit x, y;
  constraint c {
    big[1:0] != 0;
    x dist {0 := big[1:0], 1 := 1};
    y dist {0 := inner.w, 1 := 1};
  }
  function new();
    inner = new;
  endfunction
endclass

`define CHECK_SIZES(obj) \
  `check_range(obj.n, 2, 8); \
  `check_range(obj.first, 1, obj.n); \
  `check_range(obj.last, 1, obj.n);

// Counts, per element, solves where two arrays drew different buckets.
// A draw shared between arrays would give 0.
`define COUNT_DIFF(diff, x, y) \
  foreach (x[i]) if ((x[i] == 0) != (y[i] == 0)) diff++;

// Checks each k in [lo:3] is drawn and P(x == 0) = k / (k + 1)
`define CHECK_TOTAL(cls, kexpr, lo) \
    begin \
      static cls obj = new; \
      static int zero[] = new[4], total[] = new[4]; \
      int pct; \
      repeat (3 * ITERS) begin \
        randomize_result = obj.randomize(); \
        `checkd(randomize_result, 1); \
        total[kexpr]++; \
        if (obj.x == 0) zero[kexpr]++; \
      end \
      for (int k = lo; k <= 3; k++) begin \
        if (total[k] < ITERS / 2) begin \
          $write(`"%%Error: cls: too few samples for k=%0d (%0d)\n`", k, total[k]); \
          `stop; \
        end \
        pct = zero[k] * 100 / total[k]; \
        if (verbose) $display(`"cls: k=%0d P(0)=%0d%% (%0d)`", k, pct, total[k]); \
        `check_range(pct, k * 100 / (k + 1) - 12, k * 100 / (k + 1) + 12); \
      end \
    end

module t;
  localparam int ITERS = 400;
  int randomize_result;
`ifdef TEST_VERBOSE
  bit verbose = 1;
`else
  bit verbose = 0;
`endif

  initial begin
    begin
      static ClsFixed obj = new;
      static Stats s_a = new("fixed.a"), s_b = new("fixed.b");
      static int diff = 0;
      repeat (ITERS) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd(obj.a.size(), obj.n);
        `checkd(obj.b.size(), obj.n);
        foreach (obj.a[i]) begin
          s_a.add(`IS_EDGE(i, obj), obj.a[i] == 0);
          s_b.add(`IS_EDGE(i, obj), obj.b[i] == 0);
        end
        `COUNT_DIFF(diff, obj.a, obj.b);
      end
      s_a.check();
      s_b.check();
      if (diff == 0) begin
        $write("%%Error: fixed: a/b always share bucket\n");
        `stop;
      end
    end

    begin
      static ClsDynDyn obj = new;
      static Stats s_a = new("dyndyn.a"), s_b = new("dyndyn.b");
      static int diff = 0;
      repeat (ITERS) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `CHECK_SIZES(obj);
        `checkd(obj.a.size(), obj.n);
        `checkd(obj.b.size(), obj.n);
        foreach (obj.a[i]) begin
          s_a.add(`IS_EDGE(i, obj), obj.a[i] == 0);
          s_b.add(`IS_EDGE(i, obj), obj.b[i] == 0);
        end
        `COUNT_DIFF(diff, obj.a, obj.b);
      end
      s_a.check();
      s_b.check();
      if (diff == 0) begin
        $write("%%Error: dyndyn: a/b always share bucket\n");
        `stop;
      end
    end

    begin
      static ClsDynQueue obj = new;
      static Stats s_a = new("dynq.a"), s_b = new("dynq.b");
      static int diff = 0;
      repeat (ITERS) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `CHECK_SIZES(obj);
        `checkd(obj.a.size(), obj.n);
        `checkd(obj.b.size(), obj.n);
        foreach (obj.a[i]) begin
          s_a.add(`IS_EDGE(i, obj), obj.a[i] == 0);
          s_b.add(`IS_EDGE(i, obj), obj.b[i] == 0);
        end
        `COUNT_DIFF(diff, obj.a, obj.b);
      end
      s_a.check();
      s_b.check();
      if (diff == 0) begin
        $write("%%Error: dynq: a/b always share bucket\n");
        `stop;
      end
    end

    begin
      static ClsThree obj = new;
      static Stats s_a = new("three.a"), s_b = new("three.b"), s_c = new("three.c");
      static int diff_ab = 0, diff_bc = 0;
      repeat (ITERS) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `CHECK_SIZES(obj);
        `checkd(obj.a.size(), obj.n);
        `checkd(obj.b.size(), obj.n);
        `checkd(obj.c.size(), obj.n);
        foreach (obj.a[i]) begin
          s_a.add(`IS_EDGE(i, obj), obj.a[i] == 0);
          s_b.add(`IS_EDGE(i, obj), obj.b[i] == 0);
          s_c.add(`IS_EDGE(i, obj), obj.c[i] == 0);
        end
        `COUNT_DIFF(diff_ab, obj.a, obj.b);
        `COUNT_DIFF(diff_bc, obj.b, obj.c);
      end
      s_a.check();
      s_b.check();
      s_c.check();
      if (diff_ab == 0 || diff_bc == 0) begin
        $write("%%Error: three: arrays always share bucket\n");
        `stop;
      end
    end

    begin
      static ClsUnpacked obj = new;
      static Stats s_a = new("unpacked.a");
      repeat (ITERS) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `CHECK_SIZES(obj);
        foreach (obj.a[i]) s_a.add(`IS_EDGE(i, obj), obj.a[i] == 0);
      end
      s_a.check();
    end

    `CHECK_TOTAL(ClsTotal, obj.k, 1)
    `CHECK_TOTAL(ClsWeightOnly, obj.k, 0)
    `CHECK_TOTAL(ClsEnum, obj.k, 1)
    `CHECK_TOTAL(ClsStatic, obj.k, 1)
    `CHECK_TOTAL(ClsStruct, obj.s.w, 1)
    `CHECK_TOTAL(ClsDerived, obj.k, 1)

    begin
      static ClsNotPinned obj = new;
      repeat (ITERS) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `check_range(obj.big[1:0], 1, 3);
        `check_range(obj.inner.w, 1, 3);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
