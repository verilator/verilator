// DESCRIPTION: Verilator: Synchronous drives of the value last driven by the clocking block
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus_if (
    input bit clk
);
  bit w;
  clocking cb @(posedge clk);
    output w;
  endclocking
  modport tb(clocking cb);
endinterface

class Driver;
  virtual bus_if vif;
  virtual bus_if.tb mvif;
  virtual bus_if vifs[2];
  int idx;
  task run();
    repeat (2) begin
      @(vif.cb);
      vif.cb.w <= 1;
      mvif.cb.w <= 1;
      vifs[idx].cb.w <= 1;
    end
  endtask
endclass

module sub (
    input bit clk
);
  bit s;
  clocking scb @(posedge clk);
    output s;
  endclocking
endmodule

module t;
  bit clk;
  bit en = 1;
  bit k;
  bit kd;  // Driven with a cycle delay
  bit ki;  // Driven conditionally
  bit ks;  // Driven with an output skew
  string k_log;
  string kd_log;
  string ki_log;
  string ks_log;
  string s_log;
  string s0_log;
  string s1_log;
  string w_log;
  string wm_log;
  string w0_log;
  string w1_log;
  Driver drv = new;

  always #5 clk = ~clk;

  default clocking pe @(posedge clk);
    output k, kd, ki;
    output #1 ks;
  endclocking

  bus_if bus (.clk);
  bus_if mbus (.clk);
  bus_if buses[2] (.clk);
  sub sub (.clk);
  sub subs[2] (.clk);

  function automatic void log(inout string s, input bit v);
    if ($time != 0) s = {s, $sformatf("%0d@%0d ", v, $time)};
  endfunction

  always @(k) log(k_log, k);
  always @(kd) log(kd_log, kd);
  always @(ki) log(ki_log, ki);
  always @(ks) log(ks_log, ks);
  always @(sub.s) log(s_log, sub.s);
  always @(subs[0].s) log(s0_log, subs[0].s);
  always @(subs[1].s) log(s1_log, subs[1].s);
  always @(bus.w) log(w_log, bus.w);
  always @(mbus.w) log(wm_log, mbus.w);
  always @(buses[0].w) log(w0_log, buses[0].w);
  always @(buses[1].w) log(w1_log, buses[1].w);

  // A drive of the value last driven by the clocking block also assigns the signal, after it
  // was changed by a procedural assignment (IEEE 1800-2023 14.16.2)
  initial begin
    @(pe);
    pe.k <= 1;
    pe.ks <= 1;
    sub.scb.s <= 1;
    subs[1].scb.s <= 1;
    buses[0].cb.w <= 1;
    #2;
    k = 0;
    ks = 0;
    sub.s = 0;
    subs[1].s = 0;
    bus.w = 0;
    mbus.w = 0;
    buses[0].w = 0;
    buses[1].w = 0;
    @(pe);
    pe.k <= 1;
    pe.ks <= 1;
    sub.scb.s <= 1;
    subs[1].scb.s <= 1;
    buses[0].cb.w <= 1;
  end

  // A drive with a cycle delay assigns the signal only when it matures
  initial begin
    @(pe);
    pe.kd <= ##1 1;
    @(pe);
    #2 kd = 0;
    @(pe);
    pe.kd <= ##1 1;
  end

  // A conditional drive assigns the signal only when executed
  initial begin
    @(pe);
    if (en) pe.ki <= 1;
    #2 ki = 0;
    en = 0;
    @(pe);
    if (en) pe.ki <= 1;
    en = 1;
    @(pe);
    if (en) pe.ki <= 1;
  end

  initial begin
    drv.vif = bus;
    drv.mvif = mbus;
    drv.vifs[0] = buses[0];
    drv.vifs[1] = buses[1];
    drv.idx = 1;
    drv.run();
  end

  initial begin
    #50;
    `checks(k_log, "1@5 0@7 1@15 ")
    `checks(kd_log, "1@15 0@17 1@35 ")
    `checks(ki_log, "1@5 0@7 1@25 ")
    `checks(ks_log, "1@6 0@7 1@16 ")
    `checks(s_log, "1@5 0@7 1@15 ")
    `checks(s0_log, "")
    `checks(s1_log, "1@5 0@7 1@15 ")
    `checks(w_log, "1@5 0@7 1@15 ")
    `checks(wm_log, "1@5 0@7 1@15 ")
    `checks(w0_log, "1@5 0@7 1@15 ")
    `checks(w1_log, "1@5 0@7 1@15 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
