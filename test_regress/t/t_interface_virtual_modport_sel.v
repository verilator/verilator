// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Modport selection on virtual interface handles:
//   vif.modport_name   (direct)
//   obj.vif.modport_name  (chained through class member)

interface my_if (
    input logic clk
);
  logic [7:0] data;

  clocking mon_cb @(posedge clk);
    input data;
  endclocking

  modport passive_mp(clocking mon_cb);
  modport active_mp(output data);
  modport signal_mp(input data);
endinterface

class Context;
  virtual my_if vif;
endclass

class Monitor;
  virtual my_if.passive_mp mp;

  function void connect_chain(Context cntxt);
    mp = cntxt.vif.passive_mp;
  endfunction

  function void connect_tmp(Context cntxt);
    automatic virtual my_if tmp = cntxt.vif;
    mp = tmp.passive_mp;
  endfunction
endclass

class Driver;
  virtual my_if.active_mp drv;

  function void connect(Context cntxt);
    drv = cntxt.vif.active_mp;
  endfunction

  task drive(input logic [7:0] val);
    drv.data = val;
  endtask
endclass

class Reader;
  virtual my_if.signal_mp sig;

  function void connect(Context cntxt);
    sig = cntxt.vif.signal_mp;
  endfunction
endclass

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  my_if vif (.clk(clk));

  initial begin
    automatic Context c = new;
    automatic Monitor m1 = new;
    automatic Monitor m2 = new;
    automatic Driver d = new;
    automatic Reader r = new;
    c.vif = vif;

    // Connect via chain and tmp paths
    m1.connect_chain(c);
    m2.connect_tmp(c);
    d.connect(c);
    r.connect(c);

    // Drive data through active_mp, read through passive_mp and signal_mp
    d.drive(8'hAB);
    @(posedge clk);
    @(posedge clk);

    // Verify clocking-block modport (m1 = chain, m2 = tmp)
    `checkh(m1.mp.mon_cb.data, 8'hAB);
    `checkh(m2.mp.mon_cb.data, 8'hAB);

    // Verify signal modport (no clocking block)
    `checkh(r.sig.data, 8'hAB);

    // Drive new value, verify update propagates
    d.drive(8'hCD);
    @(posedge clk);
    @(posedge clk);

    `checkh(m1.mp.mon_cb.data, 8'hCD);
    `checkh(r.sig.data, 8'hCD);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
