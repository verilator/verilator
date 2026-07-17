// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// A clocking event wait executed by a process resumed mid-timestep by something
// other than the clocking event (here a mailbox get) must block until the NEXT
// clocking event, not the edge already in progress in the current timestep. The
// clocking event fires in the Observed region; a process resumed in the Active
// region of the same edge reaches the wait, suspends, and must not be woken by
// that same edge's Observed fire (which would collapse a one-clock pulse).
//
// Covers @(cb) directly, and @(vif.cb) through a (virtual) interface handle in a
// module process (static path) and a class method (dynamic path), plus a second
// interface instance (the clock-sense map is first-instance-wins) and clocks that
// are not plain interface members: via a port, and aliased inside the interface.
//
// posedges at 5, 15, 25, ...; output skew #1.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface Iface;
  logic clk = 0;
  logic sig;
  clocking cb @(posedge clk);
    default output #1;
    output sig;
  endclocking
endinterface

interface IfaceP (
    input logic clk
);
  logic sig;
  clocking cb @(posedge clk);
    default output #1;
    output sig;
  endclocking
endinterface

interface IfaceA (
    input logic clk_i
);
  logic clk;
  logic sig;
  assign clk = clk_i;
  clocking cb @(posedge clk);
    default output #1;
    output sig;
  endclocking
endinterface

class Drv;
  virtual Iface vif;
  mailbox #(int) mb;
  time t_cb;
  task run();
    int n;
    mb.get(n);  // resume mid-slot at t=15
    @(vif.cb);  // must block to t=25
    t_cb = $time;
  endtask
endclass

module t;
  timeunit 1ns; timeprecision 1ns;

  logic clk = 0;
  logic sig;
  bit seen = 0;  // did sig ever reach 1?
  always #5 clk = ~clk;

  clocking cb @(posedge clk);
    default output #1;
    output sig;
  endclocking

  Iface intf ();
  Iface intf2 ();
  IfaceP intfp (.clk(clk));
  IfaceA intfa (.clk_i(clk));

  virtual Iface vif;
  virtual Iface vif2;
  virtual IfaceP vifp;
  virtual IfaceA vifa;

  always #5 intf.clk = ~intf.clk;
  always #5 intf2.clk = ~intf2.clk;

  mailbox #(int) mb_probe = new();
  mailbox #(int) mb_pulse = new();
  mailbox #(int) mb_mod = new();
  mailbox #(int) mb_mod2 = new();
  mailbox #(int) mb_port = new();
  mailbox #(int) mb_alias = new();

  time t_first_cb, t_mod_cb, t_mod2_cb, t_port_cb, t_alias_cb;

  // Direct @(cb): timing after a mid-slot resume must be the next edge
  initial begin : timing_probe
    int n;
    mb_probe.get(n);
    @(cb);
    t_first_cb = $time;
  end

  // Direct @(cb): a one-clock pulse driven across a mid-slot resume must survive
  initial begin : pulse_driver
    int n;
    mb_pulse.get(n);
    cb.sig <= 1'b1;
    @(cb);
    cb.sig <= 1'b0;
  end
  always @(posedge clk) if (sig === 1'b1) seen = 1;

  // Static path: @(vif.cb) in a module process
  initial begin : mod_driver
    int n;
    vif = intf;
    mb_mod.get(n);
    @(vif.cb);
    t_mod_cb = $time;
  end

  // Second instance of the same interface: exercises first-instance-wins clock sense
  initial begin : mod_driver2
    int n;
    vif2 = intf2;
    mb_mod2.get(n);
    @(vif2.cb);
    t_mod2_cb = $time;
  end

  // Port clock: not a plain member, so the handle rebuild needs it kept interface-sensitive
  initial begin : port_driver
    int n;
    vifp = intfp;
    mb_port.get(n);
    @(vifp.cb);
    t_port_cb = $time;
  end

  // Clock aliased inside the interface: also not a plain member after gate optimization
  initial begin : alias_driver
    int n;
    vifa = intfa;
    mb_alias.get(n);
    @(vifa.cb);
    t_alias_cb = $time;
  end

  // Dynamic path: @(vif.cb) in a class method
  Drv d = new;

  initial begin : check
    d.vif = intf;
    d.mb = new;
    fork
      d.run();
    join_none
    repeat (2) @(posedge clk);  // t=15
    mb_probe.put(1);
    mb_pulse.put(1);
    mb_mod.put(1);
    mb_mod2.put(1);
    mb_port.put(1);
    mb_alias.put(1);
    d.mb.put(1);
    repeat (4) @(posedge clk);
    `checkd(t_first_cb, 25);  // direct @(cb)
    `checkd(seen, 1);  // one-clock pulse survived
    `checkd(t_mod_cb, 25);  // module @(vif.cb)
    `checkd(t_mod2_cb, 25);  // 2nd-instance @(vif2.cb)
    `checkd(d.t_cb, 25);  // class @(vif.cb)
    `checkd(t_port_cb, 25);  // port-clock @(vifp.cb)
    `checkd(t_alias_cb, 25);  // internally-aliased clock @(vifa.cb)
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #1000;
    `stop;
  end
endmodule
