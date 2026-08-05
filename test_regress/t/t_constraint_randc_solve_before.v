// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Phased;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
  constraint link_c {x >= {2'b00, c};}
endclass

class Layered;
  randc bit [1:0] c;
  rand bit [3:0] a;
  rand bit [3:0] b;
  rand bit [3:0] d;
  constraint order_ab {solve a before b;}
  constraint order_bd {solve b before d;}
  constraint rel_c {b > a; d > b;}
  constraint link_c {a >= {2'b00, c};}
endclass

class Limited;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
  constraint lim_c {c != 2'd3;}
endclass

class Unsat;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint bad_c {
    x > 14;
    y > x;
  }
endclass

module t;
  Phased p;
  Layered q;
  Limited r;
  Unsat u;
  bit [3:0] seen;
  int pcount[4];
  int qcount[4];
  int rcount[4];
  int ok;

  initial begin
    // Two full randc cycles; the second wraps inside a non-final solve-before phase
    p = new;
    seen = 4'b0;
    for (int i = 0; i < 8; ++i) begin
      ok = p.randomize();
      `checkd(ok, 1);
      `checkd(p.y > p.x, 1'b1);
      `checkd(p.x >= {2'b00, p.c}, 1'b1);
      seen[p.c] = 1'b1;
      ++pcount[p.c];
      if (i % 4 == 3) begin
        `checkd(seen, 4'b1111);  // Four draws covered four values, so none repeated
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 4; ++v) `checkd(pcount[v], 2);

    // Three dependency layers, so exhaustion lands two phases before the last
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

    // Hard constraint shrinks the randc domain to three values
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

    u = new;
    ok = u.randomize();
    `checkd(ok, 0);  // zero-ok: constraints are unsatisfiable

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
