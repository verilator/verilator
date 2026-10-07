// DESCRIPTION: Verilator: NBAs through handles, or in non-inlined functions, are committed with
// the other NBA updates of their time step, in the order the NBAs executed
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {int v;} state_t;

class Global;
  static int g;
endclass

interface bus (
    input bit clk
);
  int x;
  int y;
  int cnt;
  int sampled;
  logic [14:0] v;
  logic [94:0] w[3];
  logic [4096:0] big;
  always @(posedge clk) cnt <= cnt + 1;
  always @(posedge clk) sampled <= x;
  task automatic set_x(int n);
    x <= n;
  endtask
  task automatic set_y(int n);
    y <= #1 n;
  endtask
  task automatic set_v(logic [3:0] n);
    v[3:0] <= #1 n;
  endtask
  task automatic set_cnt(int n);
    cnt <= n;
  endtask
  task automatic set_global(int n);
    Global::g <= n;
  endtask
  function automatic int set_x_delay();
    x <= 1;
    return 0;
  endfunction
endinterface

class Driver;
  virtual bus vif;
  function void put(int n);
    vif.x <= n;
  endfunction
  task put_later(int n);
    vif.x <= #1 n;
  endtask
  virtual function void put_virtual(int n);
    vif.x <= n;
  endfunction
endclass

class DerivedDriver extends Driver;
  virtual function void put_virtual(int n);
    vif.x <= n + 1000;
  endfunction
endclass

class Counter;
  static int s;
  static int sd;
  task inc();
    s <= s + 1;
  endtask
  task inc_later();
    sd <= #1 sd + 10;
  endtask
endclass

module t;
  bit clk;
  bit zero;
  always #5 clk = ~clk;

  bus a (.clk);
  bus b (.clk);
  bus fn (.clk(zero));
  bus later (.clk(zero));
  bus task_later (.clk(zero));
  bus delay_nba (.clk(zero));
  bus alias_nba (.clk(zero));
  bus mixed (.clk(zero));
  bus events (.clk(zero));
  bus parts (.clk(zero));
  bus parts_task (.clk(zero));
  bus wide (.clk(zero));
  bus over (.clk(zero));
  bus comb (.clk(zero));
  bus comb_star (.clk(zero));
  bus clocked (.clk(zero));

  // A delayed NBA to a member of a struct, observed by the NBA of a clock in the same time step
  state_t s;
  bit s_clk;
  int s_seen;
  initial @(posedge s_clk) s_seen = s.v;
  initial begin
    s.v <= #1 1;
    s_clk <= #1 1;
    #2 `checkd(s_seen, 1);
  end

  // An NBA in a function of a class, through a handle, observed likewise
  Driver fn_drv = new;
  bit fn_clk;
  int fn_seen;
  initial @(posedge fn_clk) fn_seen = fn.x;
  initial begin
    fn_drv.vif = fn;
    #2;
    fn_drv.put(5);
    fn_clk <= 1;
    #1 `checkd(fn_seen, 5);
  end

  // Also a delayed one
  Driver later_drv = new;
  bit later_clk;
  int later_seen;
  initial @(posedge later_clk) later_seen = later.x;
  initial begin
    later_drv.vif = later;
    #2;
    later_drv.put_later(9);
    later_clk <= #1 1;
    #2 `checkd(later_seen, 9);
  end

  // Also a delayed one in a task of an interface, called through a handle
  virtual bus task_later_vif;
  bit task_later_clk;
  int task_later_seen;
  initial @(posedge task_later_clk) task_later_seen = task_later.y;
  initial begin
    task_later_vif = task_later;
    #2;
    task_later_vif.set_y(4);
    task_later_clk <= #1 1;
    #2 `checkd(task_later_seen, 4);
  end

  // The update of an NBA in the function computing a delay is before that of the delayed NBA
  virtual bus delay_nba_vif;
  initial begin
    delay_nba_vif = delay_nba;
    delay_nba_vif.x <= #(delay_nba_vif.set_x_delay()) 2;
    #1 `checkd(delay_nba.x, 2);
  end

  // NBAs through handles to the same interface, in the same process, update in order
  virtual bus alias_p, alias_q;
  bit alias_clk;
  always @(posedge alias_clk) begin
    alias_p.y <= #1 1;
    alias_q.y <= #1 (alias_p.y + 2);
  end
  always @(posedge alias_clk) begin
    alias_p.cnt <= 10;
    alias_q.cnt <= alias_p.cnt + 20;
  end
  initial begin
    alias_p = alias_nba;
    alias_q = alias_nba;
    #3 alias_clk = 1;
    #1 `checkd(alias_nba.cnt, 20);
    #1 `checkd(alias_nba.y, 2);
  end

  // Logic of an interface updating a variable, also updated by a task of the interface called
  // through a handle on another instance, and sampling a variable updated through a handle in the
  // same time step
  virtual bus b_vif;
  Driver a_drv = new;
  initial begin
    b_vif = b;
    a_drv.vif = a;
    a.x = 1;
    #8 b_vif.set_cnt(100);
    #7 a_drv.put(70);
    #1;
    `checkd(a.sampled, 1);
    `checkd(a.x, 70);
    #10;
    `checkd(a.sampled, 70);
    `checkd(a.cnt, 3);
    `checkd(b.cnt, 102);
  end

  // NBAs of a process and of a task through a handle, to the same variable, update in order
  virtual bus mixed_vif;
  initial begin
    mixed_vif = mixed;
    #20;
    mixed.x <= 1;
    mixed_vif.set_x(2);
    #1 `checkd(mixed.x, 2);
    mixed_vif.set_x(3);
    mixed.x <= 4;
    #1 `checkd(mixed.x, 4);
  end

  // Through a handle, with a zero delay, and with an event control
  virtual bus events_vif;
  event ev;
  initial begin
    events_vif = events;
    #20;
    events_vif.x <= #0 50;
    events_vif.x <= @(ev) 51;
    #1 `checkd(events.x, 50);
    ->ev;
    #1 `checkd(events.x, 51);
  end

  // Through a handle, of parts of variables, written by blocking assignments in the meantime
  virtual bus parts_vif;
  virtual bus parts_task_vif;
  initial begin
    parts_vif = parts;
    parts_task_vif = parts_task;
    #20;
    parts.v = 0;
    parts_task.v = 15'h7ff0;
    parts_vif.v[7:4] <= #2 4'ha;
    parts.v[14:11] <= #2 4'hb;
    parts_task_vif.set_v(4'h7);
    #1 parts.v[10:8] = 3'h5;
    #1 `checkh(parts_task.v, 15'h7ff7);
    #1 `checkh(parts.v, 15'h5da0);
  end

  // Through a handle, of wide values, with indices changing in the meantime
  virtual bus wide_vif;
  int k;
  initial begin
    wide_vif = wide;
    #20;
    wide.big = '0;
    for (k = 0; k < 3; ++k) wide_vif.w[k] <= #2 95'(k + 5) ^ {95{k[0]}};
    wide_vif.big[4096] <= #2 1'b1;
    wide_vif.big[k] <= #2 1'b1;
    k = 9;
    #3;
    `checkh(wide.w[0], 95'h5);
    `checkh(wide.w[1], ~95'h6);
    `checkh(wide.w[2], 95'h7);
    `checkh(wide.big[4096], 1'b1);
    `checkh(wide.big[3], 1'b1);
    `checkh(wide.big[9], 1'b0);
  end

  // In a function of a class, called by a clocked process, observed by another one
  Driver clocked_drv = new;
  int clocked_n;
  int clocked_seen;
  always @(posedge clk) clocked_drv.put(clocked_n);
  always @(posedge clk) clocked_seen <= clocked.x;
  initial begin
    clocked_drv.vif = clocked;
    clocked_n = 30;
    #6;
    `checkd(clocked.x, 30);
    `checkd(clocked_seen, 0);
    clocked_n = 31;
    #10;
    `checkd(clocked.x, 31);
    `checkd(clocked_seen, 30);
  end

  // In a task of an interface, to a variable not of the interface
  virtual bus global_vif;
  initial begin
    global_vif = mixed;
    #30;
    global_vif.set_global(8);
    #1 `checkd(Global::g, 8);
  end

  // In an overriding method, called through the handle of the base class
  DerivedDriver over_drv;
  Driver over_base;
  bit over_clk;
  int over_seen;
  initial @(posedge over_clk) over_seen = over.x;
  initial begin
    #20;
    over_drv = new;
    over_base = over_drv;
    over_drv.vif = over;
    over_base.put_virtual(3);
    over_clk <= 1;
    #1;
    `checkd(over.x, 1003);
    `checkd(over_seen, 1003);
  end

  // In a task of an interface, called by combinational logic
  virtual bus comb_vif = comb;
  virtual bus comb_star_vif = comb_star;
  int comb_in;
  int comb_star_in;
  int comb_out;
  int comb_star_out;
  always_comb comb_vif.set_x(comb_in);
  always @* comb_star_vif.set_x(comb_star_in);
  assign comb_out = comb.x + 1;
  assign comb_star_out = comb_star.x + 1;
  initial begin
    #30;
    comb_in = 5;
    comb_star_in = 7;
    #1;
    `checkd(comb.x, 5);
    `checkd(comb_out, 6);
    `checkd(comb_star.x, 7);
    `checkd(comb_star_out, 8);
    comb_in = 6;
    comb_star_in = 8;
    #1;
    `checkd(comb_out, 7);
    `checkd(comb_star_out, 9);
  end

  // To static members of a class
  Counter cnt1 = new;
  Counter cnt2 = new;
  bit cnt_clk;
  int cnt_seen;
  always @(posedge cnt_clk) cnt_seen <= Counter::s;
  initial begin
    #40;
    cnt1.inc();
    cnt2.inc();
    #1 `checkd(Counter::s, 1);
    cnt1.inc_later();
    Counter::sd <= #1 5;
    #2 `checkd(Counter::sd, 5);
    Counter::s <= 20;
    cnt1.inc();
    cnt_clk = 1;
    #1;
    `checkd(cnt_seen, 1);
    `checkd(Counter::s, 2);
  end

  initial begin
    #50;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
