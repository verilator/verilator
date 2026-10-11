// DESCRIPTION: Verilator: Cycle delays of synchronous drives count the target clocking block
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  bit pclk;
endpackage

interface bus_if (
    input bit clk
);
  bit w;
  bit ws;
  bit z;
  clocking cb @(posedge clk);
    output w, z;
    output #1 ws;
  endclocking
  modport tb(clocking cb);
endinterface

interface en_if (
    input bit clk
);
  bit en;
  bit y;
  clocking icb @(posedge clk iff en);
    output y;
  endclocking
endinterface

interface ev_if;
  event ev;
  bit e;
  clocking ecb @(ev);
    output e;
  endclocking
endinterface

// A class has no default clocking
class Driver;
  virtual bus_if vif;
  virtual bus_if.tb tvif;
  virtual bus_if vifs[2];
  virtual ev_if vvif;
  task run();
    @(vif.cb);
    vif.cb.w <= ##2 1;
    tvif.cb.w <= ##2 1;
    tvif.cb.ws <= ##2 1;
    vifs[0].cb.w <= ##2 1;
    vvif.ecb.e <= ##2 1;
    vif.cb.z <= ##0 1;
  endtask
endclass

// No default clocking is needed for a cycle delay in a drive
module sub (
    input bit clk,
    output bit [1:0] q
);
  bit [6:0] s;
  bit n;
  bit p;
  clocking cb @(posedge clk);
    output q, s;
  endclocking
  clocking ncb @(negedge clk);
    output n;
  endclocking
  clocking pcb @(posedge pkg::pclk);
    output p;
  endclocking
  for (genvar i = 0; i < 2; ++i) begin : g
    bit x;
    clocking cb @(posedge clk);
      output x;
    endclocking
  end
  initial begin
    @(cb);
    cb.q <= ##1 2;
  end
endmodule

module port_drv (
    bus_if b
);
  initial begin
    @(b.cb);
    b.cb.w <= ##2 1;
  end
endmodule

module t;
  bit clk;
  bit tclk;
  bit slow_clk;
  bit [1:0] v;
  bit [1:0] q;
  bit c;
  bit c0;
  bit c7;
  bit cr;
  bit cr5;
  bit d;
  int cycles = 2;
  int nocycles = 0;
  bit [6:0] cycles7 = 2;
  real rcycles = 1.6;
  string v_log;
  string q_log;
  string s_log;
  string n_log;
  string p_log;
  string x_log;
  string x0_log;
  string c_log;
  string c0_log;
  string c7_log;
  string cr_log;
  string cr5_log;
  string proc_time;
  string d_log;
  string z_log;
  string w_log;
  string tw_log;
  string tws_log;
  string w0_log;
  string w1_log;
  string mw_log;
  string pw_log;
  string y_log;
  string e_log;
  Driver drv = new;

  always #5 clk = ~clk;
  always #7 tclk = ~tclk;
  always #20 slow_clk = ~slow_clk;
  always @(clk) pkg::pclk = clk;

  default clocking slow @(posedge slow_clk);
    output d;
  endclocking

  clocking fast @(posedge clk);
    output v, c, c0, c7, cr, cr5;
  endclocking

  sub sub (
      .clk,
      .q
  );
  bus_if bus (.clk);
  // Another instance of the interface, with another clock
  bus_if tbus (.clk(tclk));
  bus_if buses[2] (.clk);
  bus_if mbus (.clk);
  bus_if pbus (.clk);
  en_if ebus (.clk);
  ev_if vbus ();
  port_drv port_drv (.b(pbus));

  virtual bus_if mvif;
  virtual en_if evif;

  initial forever #10->vbus.ev;

  always @(v) if ($time != 0) v_log = {v_log, $sformatf("%0d@%0d ", v, $time)};
  always @(q) if ($time != 0) q_log = {q_log, $sformatf("%0d@%0d ", q, $time)};
  always @(sub.s) if ($time != 0) s_log = {s_log, $sformatf("%0d@%0d ", sub.s, $time)};
  always @(sub.n) if ($time != 0) n_log = {n_log, $sformatf("%0d@%0d ", sub.n, $time)};
  always @(sub.p) if ($time != 0) p_log = {p_log, $sformatf("%0d@%0d ", sub.p, $time)};
  always @(sub.g[1].x) if ($time != 0) x_log = {x_log, $sformatf("%0d@%0d ", sub.g[1].x, $time)};
  always @(sub.g[0].x) if ($time != 0) x0_log = {x0_log, $sformatf("%0d@%0d ", sub.g[0].x, $time)};
  always @(c) if ($time != 0) c_log = {c_log, $sformatf("%0d@%0d ", c, $time)};
  always @(c0) if ($time != 0) c0_log = {c0_log, $sformatf("%0d@%0d ", c0, $time)};
  always @(c7) if ($time != 0) c7_log = {c7_log, $sformatf("%0d@%0d ", c7, $time)};
  always @(cr) if ($time != 0) cr_log = {cr_log, $sformatf("%0d@%0d ", cr, $time)};
  always @(cr5) if ($time != 0) cr5_log = {cr5_log, $sformatf("%0d@%0d ", cr5, $time)};
  always @(d) if ($time != 0) d_log = {d_log, $sformatf("%0d@%0d ", d, $time)};
  always @(bus.z) if ($time != 0) z_log = {z_log, $sformatf("%0d@%0d ", bus.z, $time)};
  always @(bus.w) if ($time != 0) w_log = {w_log, $sformatf("%0d@%0d ", bus.w, $time)};
  always @(tbus.w) if ($time != 0) tw_log = {tw_log, $sformatf("%0d@%0d ", tbus.w, $time)};
  always @(tbus.ws) if ($time != 0) tws_log = {tws_log, $sformatf("%0d@%0d ", tbus.ws, $time)};
  always @(buses[0].w) if ($time != 0) w0_log = {w0_log, $sformatf("%0d@%0d ", buses[0].w, $time)};
  always @(buses[1].w) if ($time != 0) w1_log = {w1_log, $sformatf("%0d@%0d ", buses[1].w, $time)};
  always @(mbus.w) if ($time != 0) mw_log = {mw_log, $sformatf("%0d@%0d ", mbus.w, $time)};
  always @(pbus.w) if ($time != 0) pw_log = {pw_log, $sformatf("%0d@%0d ", pbus.w, $time)};
  always @(ebus.y) if ($time != 0) y_log = {y_log, $sformatf("%0d@%0d ", ebus.y, $time)};
  always @(vbus.e) if ($time != 0) e_log = {e_log, $sformatf("%0d@%0d ", vbus.e, $time)};

  initial begin
    mvif = mbus;
    evif = ebus;
    drv.vif = bus;
    drv.tvif = tbus;
    drv.vifs[0] = buses[0];
    drv.vifs[1] = buses[1];
    drv.vvif = vbus;
    drv.run();
  end

  // Each drive counts the cycles of the target clockvar's clocking block, not of the default
  // clocking (IEEE 1800-2023 14.16)
  initial begin
    @(fast);
    fast.v <= ##2 1;
    sub.cb.s <= ##2 7'h55;
    sub.ncb.n <= ##1 1;
    sub.pcb.p <= ##1 1;
    sub.g[1].cb.x <= ##2 1;
    // The default clocking counts its cycles as before
    slow.d <= ##1 1;
    // A non-constant cycle delay is evaluated by the drive, and counted at runtime
    fast.c <= ##cycles 1;
    fast.c0 <= ##nocycles 1;
    fast.c7 <= ##cycles7 1;
    // A real cycle count is rounded (IEEE 1800-2023 6.12.1)
    fast.cr <= ##rcycles 1;
    fast.cr5 <= ##(2.5) 1;
    sub.g[0].cb.x <= ##cycles 1;
    buses[1].cb.w <= ##2 1;
    mvif.cb.w <= ##2 1;
  end

  // The clocking event of icb only occurs while en is set
  initial begin
    #1 evif.icb.y <= ##1 1;
    #20 ebus.en = 1;
  end

  // Also in a procedural cycle delay, of the default clocking
  initial begin
    #2;
    ##(1.5);
    proc_time = $sformatf("%0d", $time);
  end

  initial begin
    #100;
    `checks(v_log, "1@25 ")
    `checks(q_log, "2@15 ")
    `checks(s_log, "85@25 ")
    `checks(n_log, "1@10 ")
    `checks(p_log, "1@15 ")
    `checks(x_log, "1@25 ")
    `checks(x0_log, "1@25 ")
    `checks(c_log, "1@25 ")
    `checks(c0_log, "1@5 ")
    `checks(c7_log, "1@25 ")
    `checks(cr_log, "1@25 ")
    `checks(cr5_log, "1@35 ")
    `checks(d_log, "1@20 ")
    `checks(proc_time, "60")
    `checks(z_log, "1@5 ")
    `checks(w_log, "1@25 ")
    `checks(tw_log, "1@21 ")
    `checks(tws_log, "1@22 ")
    `checks(w0_log, "1@25 ")
    `checks(w1_log, "1@25 ")
    `checks(mw_log, "1@25 ")
    `checks(pw_log, "1@25 ")
    `checks(y_log, "1@25 ")
    `checks(e_log, "1@20 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
