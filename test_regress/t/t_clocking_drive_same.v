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
endinterface

class Driver;
  virtual bus_if vif;
  task run();
    @(vif.cb);
    vif.cb.w <= 1;
    #2 vif.w = 0;
    @(vif.cb);
    vif.cb.w <= 1;
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
  bit k;
  string k_log;
  string s_log;
  string w_log;
  Driver drv = new;

  always #5 clk = ~clk;

  clocking pe @(posedge clk);
    output k;
  endclocking

  bus_if bus (.clk);
  sub sub (.clk);

  always @(k) if ($time != 0) k_log = {k_log, $sformatf("%0d@%0d ", k, $time)};
  always @(sub.s) if ($time != 0) s_log = {s_log, $sformatf("%0d@%0d ", sub.s, $time)};
  always @(bus.w) if ($time != 0) w_log = {w_log, $sformatf("%0d@%0d ", bus.w, $time)};

  // A drive of the value last driven by the clocking block also assigns the signal, after it
  // was changed by a procedural assignment (IEEE 1800-2023 14.16.2)
  initial begin
    @(pe);
    pe.k <= 1;
    sub.scb.s <= 1;
    #2;
    k = 0;
    sub.s = 0;
    @(pe);
    pe.k <= 1;
    sub.scb.s <= 1;
  end

  initial begin
    drv.vif = bus;
    drv.run();
  end

  initial begin
    #30;
    `checks(k_log, "1@5 0@7 1@15 ")
    `checks(s_log, "1@5 0@7 1@15 ")
    `checks(w_log, "1@5 0@7 1@15 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
