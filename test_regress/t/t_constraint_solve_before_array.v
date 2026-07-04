// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// solve...before over array rand variables: each solved layer is pinned
// per element so the phased solve round-trips.
class OneD;
  rand int unsigned a[2];
  rand int unsigned b[2];
  constraint c {
    solve a before b;
    foreach (b[i]) b[i] == a[i] + 1;
  }
endclass

class TwoD;
  rand int unsigned a[2][2];
  rand int unsigned b[2][2];
  constraint c {
    solve a before b;
    foreach (b[i, j]) b[i][j] == a[i][j] + 1;
  }
endclass

class Mul;  // the rv_timer ticks_c shape: mul across a solved layer
  rand int unsigned prescale[2];
  rand int unsigned ticks[2];
  constraint c {
    solve prescale before ticks;
    foreach (ticks[i]) (ticks[i] * (prescale[i] + 1)) <= 5000;
  }
endclass

class Chain;  // three-layer chain
  rand int unsigned a[2];
  rand int unsigned b[2];
  rand int unsigned d[2];
  constraint c {
    solve a before b;
    solve b before d;
    foreach (a[i]) a[i] inside {[1:10]};
    foreach (b[i]) b[i] == a[i] * 2;
    foreach (d[i]) d[i] == b[i] + a[i];
  }
endclass

class Que;  // dynamic container solved before a scalar
  rand int unsigned q[$];
  rand int unsigned s;
  constraint c {
    q.size() == 3;
    solve q before s;
    foreach (q[i]) q[i] inside {[1:10]};
    s == q[0] + q[1] + q[2];
  }
endclass

module t;
  OneD o1;
  TwoD o2;
  Mul om;
  Chain oc;
  Que oq;
  int ok;
  initial begin
    o1 = new;
    o2 = new;
    om = new;
    oc = new;
    oq = new;
    for (int i = 0; i < 10; ++i) begin
      ok = o1.randomize();
      `checkd(ok, 1);
      `checkd(o1.b[0], o1.a[0] + 1);
      `checkd(o1.b[1], o1.a[1] + 1);

      ok = o2.randomize();
      `checkd(ok, 1);
      `checkd(o2.b[0][0], o2.a[0][0] + 1);
      `checkd(o2.b[1][1], o2.a[1][1] + 1);

      ok = om.randomize();
      `checkd(ok, 1);
      if ((om.ticks[0] * (om.prescale[0] + 1)) > 5000) `checkd(0, 1);

      ok = oc.randomize();
      `checkd(ok, 1);
      `checkd(oc.b[0], oc.a[0] * 2);
      `checkd(oc.d[1], oc.b[1] + oc.a[1]);

      ok = oq.randomize();
      `checkd(ok, 1);
      `checkd(oq.s, oq.q[0] + oq.q[1] + oq.q[2]);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
