// DESCRIPTION: Verilator: Pending intra-assignment NBAs keep their own values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus (
    input bit clk
);
  int v;
  int p;
  int r;
  int s;
  bit w;
  clocking cb @(posedge clk);
    output w;
  endclocking
endinterface

class Driver;
  virtual bus vif;
  task nba(int val);
    vif.v <= #5 val;
  endtask
  task drive();
    vif.cb.w <= ##2 1;
  endtask
endclass

module t;
  bit clk;
  bit clk2;
  int x;
  bit [2:0] y;
  int z[3];
  bit [1:0] q;
  int c;
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
  virtual bus mvif;
  virtual bus vifs[2];
  int k;
  Driver drv = new;

  always #5 clk = ~clk;
  always #7 clk2 = ~clk2;

  default clocking cb @(posedge clk);
    output q, c;
  endclocking

  bus a (.clk);
  bus b (.clk(clk2));

  task automatic pulse(bit [1:0] v);
    cb.q <= ##2 v;
  endtask

  function automatic int count(int n);
    return n;
  endfunction

  always @(x) if ($time != 0) x_log = {x_log, $sformatf("%0d@%0d ", x, $time)};
  always @(y) if ($time != 0) y_log = {y_log, $sformatf("%0d@%0d ", y, $time)};
  always @(q) if ($time != 0) q_log = {q_log, $sformatf("%0d@%0d ", q, $time)};
  always @(c) if ($time != 0) c_log = {c_log, $sformatf("%0d@%0d ", c, $time)};
  always @(a.v) if ($time != 0) a_log = {a_log, $sformatf("%0d@%0d ", a.v, $time)};
  always @(b.v) if ($time != 0) b_log = {b_log, $sformatf("%0d@%0d ", b.v, $time)};
  always @(a.w) if ($time != 0) aw_log = {aw_log, $sformatf("%0d@%0d ", a.w, $time)};
  always @(b.w) if ($time != 0) bw_log = {bw_log, $sformatf("%0d@%0d ", b.w, $time)};

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

  // Also when its count is computed by a function
  initial begin
    for (int i = 1; i <= 3; ++i) begin
      @(cb);
      cb.c <= ##(count(i)) i;
    end
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

  // Also a pending drive, counting the cycles of the interface referenced when it was scheduled
  initial begin
    @(a.cb);
    drv.vif = a;
    drv.drive();
    drv.vif = b;
  end

  initial begin
    #60;
    `checks(x_log, "1@5 2@6 3@7 ")
    `checks(y_log, "7@5 ")
    `checks(z_at4, "0 0 0")
    `checks(z_at6, "1 2 3")
    `checks(q_log, "1@25 2@35 ")
    `checks(c_log, "1@15 2@35 3@55 ")
    `checks(a_log, "7@5 9@6 5@7 ")
    `checks(b_log, "")
    `checks($sformatf("%0d %0d %0d %0d %0d %0d", a.p, b.p, a.r, b.r, a.s, b.s), "3 0 4 0 5 0")
    // Last, as VCS drives the interface referenced when the drive matures
    `checks(aw_log, "1@25 ")
    `checks(bw_log, "")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
