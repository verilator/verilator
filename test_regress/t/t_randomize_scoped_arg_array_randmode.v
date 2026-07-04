// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Scoped this.randomize(scalar) while OTHER rand members are arrays that stay
// frozen (rand_mode machinery engaged): the frozen array's element constraint
// must format as a valid (select ...) pin, not (select <whole-array> idx).
typedef int unsigned uint;

class Base;
  rand uint delay;
  rand uint guard;  // gets rand_mode(0) to engage the per-var mode machinery
  constraint delay_c {delay inside {[1:100]};}
  function int rd();
    return this.randomize(delay);
  endfunction
endclass

class Unpacked extends Base;
  rand uint a[3];
  constraint c {foreach (a[i]) a[i] inside {[1:10]};}
endclass

class Unpacked2D extends Base;
  rand uint a[2][2];
  constraint c {foreach (a[i, j]) a[i][j] inside {[1:10]};}
endclass

class Queue extends Base;
  rand uint a[$];
  constraint c {
    a.size() == 3;
    foreach (a[i]) a[i] inside {[1:10]};
  }
endclass

class Dyn extends Base;
  rand uint a[];
  constraint c {
    a.size() == 3;
    foreach (a[i]) a[i] inside {[1:10]};
  }
endclass

/* verilator lint_off SIDEEFFECT */
class AssocStr extends Base;
  rand uint amap[string];
  constraint c {
    amap["alice"] inside {[1:10]};
    amap["bob"] inside {[20:30]};
  }
  function new();
    amap = '{"alice": 5, "bob": 25};
  endfunction
endclass

class EmptyAssoc extends Base;  // never populated: frozen default 0 violates
  rand uint amap[string];
  constraint c {amap["alice"] inside {[1:10]};}
endclass

class AssocInt extends Base;
  rand uint imap[int];
  constraint c {foreach (imap[k]) imap[k] inside {[1:10]};}
  /* verilator lint_on SIDEEFFECT */
  function new();
    imap[2] = 1;
    imap[5] = 1;
  endfunction
endclass

class NoModes;  // no rand_mode() call anywhere; scoped arg only
  rand uint x, y;
  rand uint arr[2];
  constraint c {
    x inside {[1:100]};
    y inside {[1:100]};
    foreach (arr[i]) arr[i] inside {[1:10]};
  }
  function int rx();
    return this.randomize(x);
  endfunction
endclass

module t;
  int ok;
  initial begin
    Unpacked u;
    Unpacked2D u2;
    Queue q;
    Dyn d;
    uint snap1[3];
    uint snap2[2][2];
    uint snapq[$];
    uint snapd[];

    u = new;
    ok = u.randomize();
    `checkd(ok, 1);
    u.guard.rand_mode(0);
    snap1 = u.a;
    for (int i = 0; i < 5; ++i) begin
      ok = u.rd();
      `checkd(ok, 1);
      if (u.a !== snap1) `checkd(0, 1);
      if (u.delay < 1 || u.delay > 100) `checkd(0, 1);
    end

    u2 = new;
    ok = u2.randomize();
    `checkd(ok, 1);
    u2.guard.rand_mode(0);
    snap2 = u2.a;
    for (int i = 0; i < 5; ++i) begin
      ok = u2.rd();
      `checkd(ok, 1);
      if (u2.a !== snap2) `checkd(0, 1);
    end

    q = new;
    ok = q.randomize();
    `checkd(ok, 1);
    q.guard.rand_mode(0);
    snapq = q.a;
    for (int i = 0; i < 5; ++i) begin
      ok = q.rd();
      `checkd(ok, 1);
      if (q.a !== snapq) `checkd(0, 1);
    end

    d = new;
    ok = d.randomize();
    `checkd(ok, 1);
    d.guard.rand_mode(0);
    snapd = d.a;
    for (int i = 0; i < 5; ++i) begin
      ok = d.rd();
      `checkd(ok, 1);
      if (d.a !== snapd) `checkd(0, 1);
    end

    // Associative array with string-literal keys stays frozen.
    begin
      AssocStr as;
      uint snapa, snapb;
      as = new;
      ok = as.randomize();
      `checkd(ok, 1);
      as.guard.rand_mode(0);
      snapa = as.amap["alice"];
      snapb = as.amap["bob"];
      for (int i = 0; i < 5; ++i) begin
        ok = as.rd();
        `checkd(ok, 1);
        `checkd(as.amap["alice"], snapa);
        `checkd(as.amap["bob"], snapb);
        if (as.delay < 1 || as.delay > 100) `checkd(0, 1);
      end
    end

    // Associative array with int keys under foreach stays frozen.
    begin
      AssocInt ai;
      uint snap2, snap5;
      ai = new;
      ok = ai.randomize();
      `checkd(ok, 1);
      ai.guard.rand_mode(0);
      snap2 = ai.imap[2];
      snap5 = ai.imap[5];
      for (int i = 0; i < 5; ++i) begin
        ok = ai.rd();
        `checkd(ok, 1);
        `checkd(ai.imap[2], snap2);
        `checkd(ai.imap[5], snap5);
      end
    end

    // Never-populated assoc array: the declared solver domain must still match
    // the constraint keys (128-bit string); the frozen default 0 then honestly
    // violates membership on the scoped call.
    begin
      EmptyAssoc ea;
      ea = new;
      ea.guard.rand_mode(0);
      for (int i = 0; i < 3; ++i) begin
        ok = ea.rd();
        `checkd(ok, 0);
      end
    end

    // Scoped randomize with NO rand_mode machinery engaged elsewhere:
    // non-argument members stay frozen (IEEE 1800-2023 18.11).
    begin
      NoModes nm;
      uint snapy;
      uint snaparr[2];
      nm = new;
      ok = nm.randomize();
      `checkd(ok, 1);
      snapy = nm.y;
      snaparr = nm.arr;
      for (int i = 0; i < 10; ++i) begin
        ok = nm.rx();
        `checkd(ok, 1);
        `checkd(nm.y, snapy);
        if (nm.arr !== snaparr) `checkd(0, 1);
        if (nm.x < 1 || nm.x > 100) `checkd(0, 1);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
