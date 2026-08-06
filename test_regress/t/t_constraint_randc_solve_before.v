// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// randc values excluded by the value of another rand variable: c cannot be 3
class Phased;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > {2'b00, x};}
  constraint link_c {c < x;}
endclass

// Three dependency layers, so exhaustion lands two phases before the last
class Layered;
  randc bit [1:0] c;
  rand bit [3:0] a;
  rand bit [3:0] b;
  rand bit [3:0] d;
  constraint order_ab {solve a before b;}
  constraint order_bd {solve b before d;}
  constraint rel_c {
    b > a;
    d > b;
  }
  constraint link_c {a >= {2'b00, c};}
endclass

// Hard constraint shrinks the randc domain to three values
class Limited;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
  constraint lim_c {c != 2'd3;}
endclass

// randc pins a solve-before variable, so only randc-first keeps the cycle
class Ordered;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [1:0] y;
  constraint order_c {solve x before y;}
  constraint tie_c {x == c;}
  constraint rel_c {y == ~x;}
endclass

// Unsatisfiable before any randc value is recorded
class Unsat;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
endclass

module t;
  Phased p;
  Layered q;
  Limited r;
  Ordered o;
  Unsat u;
  bit [3:0] seen;
  int pcount[4];
  int qcount[4];
  int rcount[4];
  int ocount[4];
  int ok;
  int psolved;

  initial begin
    // c == 3 satisfies no x
    p = new;
    seen = 4'b0;
    psolved = 0;
    for (int i = 0; i < 12 && psolved < 9; ++i) begin
      if (p.randomize() == 1) begin
        `checkd(p.y > {2'b00, p.x}, 1'b1);
        `checkd(p.c < p.x, 1'b1);
        seen[p.c] = 1'b1;
        ++pcount[p.c];
        ++psolved;
        if (psolved % 3 == 0) begin
          `checkd(seen, 4'b0111);  // Three draws covered three values, so none repeated
          seen = 4'b0;
        end
      end
    end
    `checkd(psolved, 9);  // Three cycles of three solvable values
    for (int v = 0; v < 3; ++v) `checkd(pcount[v], 3);
    `checkd(pcount[3], 0);  // zero-ok: c == 3 satisfies no x

    q = new;
    seen = 4'b0;
    for (int i = 0; i < 8; ++i) begin
      ok = q.randomize();
      `checkd(ok, 1);
      `checkd(q.b > q.a, 1'b1);
      `checkd(q.d > q.b, 1'b1);
      `checkd(q.a >= {2'b00, q.c}, 1'b1);
      seen[q.c] = 1'b1;
      ++qcount[q.c];
      if (i % 4 == 3) begin
        `checkd(seen, 4'b1111);
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 4; ++v) `checkd(qcount[v], 2);

    r = new;
    seen = 4'b0;
    for (int i = 0; i < 6; ++i) begin
      ok = r.randomize();
      `checkd(ok, 1);
      `checkd(r.y > r.x, 1'b1);
      seen[r.c] = 1'b1;
      ++rcount[r.c];
      if (i % 3 == 2) begin
        `checkd(seen, 4'b0111);
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 3; ++v) `checkd(rcount[v], 2);
    `checkd(rcount[3], 0);  // zero-ok: excluded by lim_c

    o = new;
    seen = 4'b0;
    for (int i = 0; i < 8; ++i) begin
      ok = o.randomize();
      `checkd(ok, 1);
      `checkd(o.x, o.c);
      `checkd(o.y, ~o.x);
      seen[o.x] = 1'b1;
      ++ocount[o.x];
      if (i % 4 == 3) begin
        `checkd(seen, 4'b1111);
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 4; ++v) `checkd(ocount[v], 2);

    // Fails with an empty cycle, then the object still randomizes
    u = new;
    ok = u.randomize() with {
      x > 14;
      y > x;
    };
    `checkd(ok, 0);  // zero-ok: constraints are unsatisfiable
    ok = u.randomize();
    `checkd(ok, 1);
    `checkd(u.y > u.x, 1'b1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
