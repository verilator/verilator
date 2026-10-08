// DESCRIPTION: Verilator: Pending intra-assignment NBAs keep their own values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  int f;
  int g;
} pair_t;

interface bus (
    input bit clk
);
  int v;
  int p;
  int r;
  int s;
  int t;
  pair_t st;
  pair_t sa[2];
  int n;
  bit w;
  bit u;
  pair_t d;
  int e;
  bit f;
  bit h;
  int o;
  int cnt;
  clocking cb @(posedge clk);
    output w, u, d, e, f, h;
  endclocking
  always @(posedge clk) cnt <= cnt + 1;
  task automatic set_cnt(int val);
    cnt <= val;
  endtask
endinterface

class Driver;
  virtual bus vif;
  virtual bus vifs[2];
  int idx;
  task nba(int val);
    vif.v <= #5 val;
  endtask
  task drive();
    vif.cb.w <= ##2 1;
    vif.cb.d.g <= ##2 1;
  endtask
  task drive_at(int i);
    vifs[i].cb.u <= ##2 1;
  endtask
  task order(int val);
    vif.o <= #4 val;
  endtask
endclass

class Capture;
  process seen;
  function int delay();
    seen = process::self();
    return 5;
  endfunction
endclass

module t;
  bit clk;
  bit clk2;
  int x;
  bit [2:0] y;
  int z[3];
  bit [1:0] q;
  int c;
  int dc;
  int nd;
  int nd_n;
  int nd_z;
  int lw;
  string x_log;
  string y_log;
  string z_at4;
  string z_at6;
  string q_log;
  string c_log;
  string a_log;
  string b_log;
  string aw_log;
  string bw_log;
  string u_log;
  string d_log;
  string dc_log;
  string nd_log;
  string lw_log;
  string e_log;
  string h_log;
  virtual bus mvif;
  virtual bus vifs[2];
  int k;
  virtual bus svif;
  virtual bus svifs[2];
  pair_t sarr[2];
  virtual bus rvif;
  virtual bus hvifs[2];
  int hk;
  int oa[2];
  int ob[2];
  bit [1:0] op;
  bit [1:0] oq;
  real ora[2];
  string osa[2];
  real ors;
  pair_t oua[2];
  pair_t opr;
  int oi;
  int ta[2];
  int tx;
  pair_t ts[2];
  int ti;
  int tz;
  int te;
  event tev;
  bit [9:2] tp;
  bit [9:2] tq;
  bit [7:1] tr;
  virtual bus ovif;
  virtual bus cvif;
  Driver drv = new;
  Driver dh;
  Driver odrv = new;
  bit cat_a, cat_b, cat_c, cat_d, cat_e, cat_f, cat_g, cat_h;
  int dly_calls;
  string cat_log;
  event cev;
  Capture cap = new;
  process cap_parent;
  int cap_x;

  always #5 clk = ~clk;
  always #7 clk2 = ~clk2;

  default clocking cb @(posedge clk);
    output q, c, dc, nd, lw;
  endclocking

  bus a (.clk);
  bus b (.clk(clk2));

  task automatic pulse(bit [1:0] v);
    cb.q <= ##2 v;
  endtask

  function automatic int count(int n);
    int r = 0;
    for (int j = 0; j < n; ++j) r += 1;
    return r;
  endfunction

  function automatic int bump(ref int n);
    n = n + 1;
    return n;
  endfunction

  task automatic send(input int n);
    cb.dc <= ##(bump(n)) 7;
  endtask

  task automatic send_h(virtual bus h);
    h.cb.e <= ##(h.n) 7;
  endtask

  function automatic int retarget();
    rvif = b;
    return 1;
  endfunction

  function automatic int idx_of(int i);
    return i;
  endfunction

  function automatic int dly();
    ++dly_calls;
    return 5;
  endfunction

  always @(x) if ($time != 0) x_log = {x_log, $sformatf("%0d@%0d ", x, $time)};
  always @(y) if ($time != 0) y_log = {y_log, $sformatf("%0d@%0d ", y, $time)};
  always @(q) if ($time != 0) q_log = {q_log, $sformatf("%0d@%0d ", q, $time)};
  always @(c) if ($time != 0) c_log = {c_log, $sformatf("%0d@%0d ", c, $time)};
  always @(dc) if ($time != 0) dc_log = {dc_log, $sformatf("%0d@%0d ", dc, $time)};
  always @(nd) if ($time != 0) nd_log = {nd_log, $sformatf("%0d@%0d ", nd, $time)};
  always @(lw) if ($time != 0) lw_log = {lw_log, $sformatf("%0d@%0d ", lw, $time)};
  always @(a.e) if ($time != 0) e_log = {e_log, $sformatf("a%0d@%0d ", a.e, $time)};
  always @(b.e) if ($time != 0) e_log = {e_log, $sformatf("b%0d@%0d ", b.e, $time)};
  always @(a.h) if ($time != 0) h_log = {h_log, $sformatf("a%0d@%0d ", a.h, $time)};
  always @(b.h) if ($time != 0) h_log = {h_log, $sformatf("b%0d@%0d ", b.h, $time)};
  always @(a.v) if ($time != 0) a_log = {a_log, $sformatf("%0d@%0d ", a.v, $time)};
  always @(b.v) if ($time != 0) b_log = {b_log, $sformatf("%0d@%0d ", b.v, $time)};
  always @(a.w) if ($time != 0) aw_log = {aw_log, $sformatf("%0d@%0d ", a.w, $time)};
  always @(b.w) if ($time != 0) bw_log = {bw_log, $sformatf("%0d@%0d ", b.w, $time)};
  always @(a.u) if ($time != 0) u_log = {u_log, $sformatf("a%0d@%0d ", a.u, $time)};
  always @(b.u) if ($time != 0) u_log = {u_log, $sformatf("b%0d@%0d ", b.u, $time)};
  always @(a.d.g) if ($time != 0) d_log = {d_log, $sformatf("a%0d@%0d ", a.d.g, $time)};
  always @(b.d.g) if ($time != 0) d_log = {d_log, $sformatf("b%0d@%0d ", b.d.g, $time)};

  // Each pending update keeps the value it was scheduled with
  initial begin
    for (int i = 1; i <= 3; ++i) begin
      x <= #5 i;
      #1;
    end
  end

  // Pending updates maturing together each update their own target
  initial begin
    for (int i = 0; i < 3; ++i) begin
      y[i] <= #5 1'b1;
      z[i] <= #5 i + 1;
    end
    #4 z_at4 = $sformatf("%0d %0d %0d", z[0], z[1], z[2]);
    #2 z_at6 = $sformatf("%0d %0d %0d", z[0], z[1], z[2]);
  end

  // Each pending drive from the same inlined call counts its own cycles
  initial begin
    for (int i = 1; i <= 2; ++i) begin
      @(cb);
      pulse(2'(i));
    end
  end

  // Also when its count is computed by a function, with a loop
  initial begin
    for (int i = 1; i <= 3; ++i) begin
      @(cb);
      cb.c <= ##(count(i)) i;
    end
  end

  // Also when another process changes the count while the drives are pending
  initial begin
    nd_n = 3;
    nd_z = 10;
    for (int i = 0; i < 3; ++i) begin
      @(cb);
      cb.nd <= ##(nd_n) nd_z + 1;
      nd_z += 10;
    end
  end
  initial begin
    #12 nd_n = 1;
    #10 nd_n = 2;
  end

  // Of drives maturing in the same cycle, the last one executed wins (IEEE 1800-2023 14.16.2)
  initial begin
    @(cb);
    cb.lw <= ##2 1;
    @(cb);
    cb.lw <= ##1 2;
  end

  // Also with an index selecting the handle computed by a function
  initial begin
    hvifs[0] = a;
    hvifs[1] = b;
    @(a.cb);
    hk = $urandom_range(0, 0);
    hvifs[idx_of(hk)].cb.h <= ##2 1;
    hk = 1;
  end

  // Pending updates of evaluated targets are in order with the time step's other updates, also
  // when scheduled before them (IEEE 1800-2023 4.6)
  initial begin
    oi = $urandom_range(0, 0);
    oa[oi] <= #5 1;
    ob[0] <= #5 1;
    op[oi] <= #5 1;
    oq[0] <= #5 1;
    ora[oi] <= #5 1.5;
`ifndef VCS
    // VCS does not allow NBAs to strings
    osa[oi] <= #5 "s";
`endif
    ors <= #5 2.5;
    oua[1].f <= #5 3;
    opr.f = 4;
    oua[oi] <= #5 opr;
    #1 ob[oi] <= #4 2;
    oq[oi] <= #4 0;
    #4 oa[oi] <= 2;
    op[oi] <= 0;
  end

  // Updates of NBAs are performed in the order the NBAs were executed (IEEE 1800-2023 4.6), also
  // when pending updates become ready in another order: of a variable, of an element of an array
  // of structs, and of an interface member through handles, a class method and directly
  initial begin
    ti = $urandom_range(0, 0);
    odrv.vif = a;
    ovif = a;
    #1 ta[ti] <= #4 1;
    tx <= #4 1;
    ts[ti].f <= #4 1;
    tr[ti+1+:3] <= #4 3'h5;
    odrv.order(1);
    ovif.o <= #4 2;
    odrv.vif = b;
    ovif = b;
  end
  initial begin
    #5 ta[0] <= 2;
    tx <= 2;
    ts[0].f <= 2;
    a.o <= 3;
    tr[ti+1+:3] <= 3'h2;
  end

  // Also with a zero delay, and when a pending update becomes ready in a later NBA region
  initial begin
    tz <= #0 1;
    tz <= 2;
    te <= @(tev) 1;
    te <= 2;
    @(te);
    ->tev;
  end

  // Also of parts of variables, written by blocking assignments in the meantime
  initial begin
    tp <= #5 8'h12;
    tq[5:2] <= #5 4'ha;
    #1 tp[5:2] <= #4 4'hb;
    #1 begin
      tp[9:6] = 4'hf;
      tq[9:6] = 4'hf;
    end
  end

  // Also of a variable updated by the NBAs of a process and of a task of an interface
  initial begin
    cvif = a;
    #8 cvif.set_cnt(100);
  end

  // Also by functions of the arguments of a task, changing them or the handle
  initial begin
    a.n = 2;
    rvif = a;
    @(cb);
    send(1);
    send_h(a);
    rvif.cb.f <= ##(retarget()) 1;
  end

  // A pending update targets the interface referenced when it was scheduled (IEEE 1800-2023
  // 10.4.2), in a class and in a module
  initial begin
    drv.vif = a;
    drv.nba(7);
    drv.vif = b;
    mvif = a;
    mvif.v <= #6 9;
    mvif = b;
    drv.vif = a;
    drv.vif.v <= #7 5;
    drv.vif = b;
    dh = new;
    dh.vif = a;
    dh.vif.v <= #8 3;
    dh = drv;
  end

  // Also without delay, through a handle, a class member or an array element
  initial begin
    mvif = a;
    mvif.p <= 3;
    mvif = b;
    drv.vif = a;
    drv.vif.r <= 4;
    drv.vif = b;
    vifs[0] = a;
    vifs[1] = b;
    k = 0;
    vifs[k].s <= 5;
    k = 1;
    vifs[0] = b;
  end

  // Also below members of unpacked structs, and with an index selecting a class member. The
  // delay makes this a process with timing, which updates also arrays of structs this way.
  initial begin
    drv.idx = 1;
    svif = a;
    svif.st.f <= 6;
    svif.sa[drv.idx].g <= 7;
    svif.sa[drv.idx].f <= #2 10;
    sarr[drv.idx].f <= 8;
    svifs[0] = b;
    svifs[1] = a;
    svifs[drv.idx].t <= 9;
    drv.idx = 0;
    svif = b;
    svifs[1] = b;
    #1;
  end

  // Also a pending drive, counting the cycles of the interface referenced when it was scheduled,
  // also to a member of a clockvar, and through an interface selected from an array
  initial begin
    drv.vifs[0] = a;
    drv.vifs[1] = b;
    @(a.cb);
    drv.vif = a;
    drv.drive();
    drv.vif = b;
    drv.drive_at(0);
    drv.vifs[0] = b;
  end

  // A concatenation of targets is updated after the timing control once, evaluated once
  initial begin
    {cat_a, cat_b} = #5 2'b11;
    cat_log = {cat_log, $sformatf("%0b%0b@%0t ", cat_a, cat_b, $time)};
    {cat_c, cat_d} <= #(dly()) 2'b11;
    {cat_g, cat_h} <= @(cev) 2'b11;
    {cat_e, cat_f} = @(cev) 2'b11;
    cat_log = {cat_log, $sformatf("%0b%0b@%0t ", cat_e, cat_f, $time)};
  end
  initial #7->cev;

  // The process executing the NBA evaluates its delay
  initial begin
    cap_parent = process::self();
    cap_x <= #(cap.delay()) 1;
    #6;
  end

  initial begin
    #60;
    `checks(x_log, "1@5 2@6 3@7 ")
    `checks(y_log, "7@5 ")
    `checks(z_at4, "0 0 0")
    `checks(z_at6, "1 2 3")
    `checks(q_log, "1@25 2@35 ")
    `checks(c_log, "1@15 2@35 3@55 ")
    `checks(dc_log, "7@25 ")
    `checks(nd_log, "21@25 11@35 31@45 ")
    `checks(lw_log, "2@25 ")
    `checks(e_log, "a7@25 ")
    `checks($sformatf("%0b", rvif == b), "1")
    `checks($sformatf("%0.1f %0.1f %0d %0d", ora[0], ors, oua[0].f, oua[1].f), "1.5 2.5 4 3")
`ifndef VCS
    `checks(osa[0], "s")
`endif
    `checks(a_log, "7@5 9@6 5@7 3@8 ")
    `checks(b_log, "")
    `checks($sformatf("%0d %0d %0d %0d %0d %0d", a.p, b.p, a.r, b.r, a.s, b.s), "3 0 4 0 5 0")
    `checks($sformatf("%0d %0d %0d %0d", a.st.f, b.st.f, a.t, b.t), "6 0 9 0")
    `checks($sformatf("%0d %0d %0d %0d", a.sa[0].f, a.sa[0].g, a.sa[1].f, a.sa[1].g), "0 0 10 7")
    `checks($sformatf("%0d %0d %0d %0d", b.sa[0].f, b.sa[0].g, b.sa[1].f, b.sa[1].g), "0 0 0 0")
    `checks($sformatf("%0d %0d", sarr[0].f, sarr[1].f), "0 8")
    `checks($sformatf("%0d %0d %x %x", tz, te, tp, tq), "2 1 1b fa")
    `checks($sformatf("%0d %0d", a.cnt, b.cnt), "105 4")
    `checks(cat_log, "11@5 11@7 ")
    `checks($sformatf("%0b%0b %0b%0b", cat_c, cat_d, cat_g, cat_h), "11 11")
    `checks($sformatf("%0b %0d", cap.seen == cap_parent, cap_x), "1 1")
    // Last, as VCS performs the pending updates of intra-assignment delays after the time step's
    // other NBA updates, drives the interface referenced when a drive matures, and evaluates the
    // delay of an NBA to a concatenation for each part
    `checks($sformatf("%0d", dly_calls), "1")
    `checks($sformatf("%0d %0d %0d %0d", oa[0], ob[0], op[0], oq[0]), "2 2 0 0")
    `checks($sformatf("%0d %0d %0d %0d %0d %0d", ta[0], tx, ts[0].f, a.o, b.o, tr), "2 2 2 3 0 2")
    `checks(aw_log, "1@25 ")
    `checks(bw_log, "")
    `checks(d_log, "a1@25 ")
`ifndef MODEL_TECH
    // Questa drops these drives, through an interface selected from an array, changed while
    // pending
    `checks(u_log, "a1@25 ")
    `checks(h_log, "a1@25 ")
`endif
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
