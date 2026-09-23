// DESCRIPTION: Verilator: Program synchronous drives and NBAs in the Re-NBA region
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus_if (
    input bit clk
);
  bit valid;
  bit [7:0] data;
  bit [1:0] req;
  default clocking cb @(posedge clk);
    output #0 valid, req;
  endclocking
  task automatic pulse(bit [1:0] value);
    cb.req <= value;
    cb.req <= ##1 0;
  endtask
endinterface

class Monitor;
  virtual bus_if vif;
  bit [7:0] seen;
  task run();
    @(posedge vif.valid);
    seen = vif.data;
  endtask
endclass

class Driver;
  virtual bus_if vif;
  task run();
    @(vif.cb);
    vif.data <= 8'hc3;
    vif.cb.valid <= 1;
    vif.pulse(1);
    @(vif.cb);
    vif.pulse(2);
  endtask
endclass

module t;
  bit clk;
  bit [1:0] req;
  bit [1:0] task_req;
  bit [1:0] zreq;
  bit [1:0] mzreq;
  bit valid;
  bit [7:0] data;
  bit task_valid;
  bit [7:0] task_data;
  bit a = 1'b1;
  event x;
  string req_log;
  string task_req_log;
  string zreq_log;
  string mzreq_log;
  string a_log;
  string bus_req_log;

  always #5 clk = ~clk;

  bus_if bus (.clk);

  clocking vck @(posedge clk);
    output #0 valid, task_valid;
  endclocking

  // IEEE 1800-2023 14.16.2: 'a' glitches 1 -> 0 -> 1 at the first posedge of clk
  default clocking cb @(posedge clk);
    output a, mzreq;
  endclocking
  initial begin
    ##1;
    cb.a <= 1'b0;
    // '##0' has no effect in a synchronous drive (IEEE 1800-2023 14.11)
    cb.mzreq <= ##0 1;
    cb.mzreq <= 2;
    @(x);  // Triggered by the program in the same time step
    cb.a <= 1'b1;
  end

  always @(req) if ($time != 0) req_log = {req_log, $sformatf("%0d@%0d ", req, $time)};
  always @(task_req) begin
    if ($time != 0) task_req_log = {task_req_log, $sformatf("%0d@%0d ", task_req, $time)};
  end
  always @(zreq) if ($time != 0) zreq_log = {zreq_log, $sformatf("%0d@%0d ", zreq, $time)};
  always @(mzreq) if ($time != 0) mzreq_log = {mzreq_log, $sformatf("%0d@%0d ", mzreq, $time)};
  always @(a) if ($time != 0) a_log = {a_log, $sformatf("%0d@%0d ", a, $time)};
  always @(bus.req) begin
    if ($time != 0) bus_req_log = {bus_req_log, $sformatf("%0d@%0d ", bus.req, $time)};
  end

  drv drv (
      .clk,
      .req,
      .task_req,
      .zreq
  );
  chk chk ();
endmodule

program drv (
    input bit clk,
    output bit [1:0] req,
    output bit [1:0] task_req,
    output bit [1:0] zreq
);
  default clocking dcb @(posedge clk);
    output req, task_req, zreq;
  endclocking

  task automatic pulse(bit [1:0] value);
    if (value == 0) return;
    dcb.task_req <= value;
    dcb.task_req <= ##1 0;
  endtask

  // A matured '##1' drive must not override a drive executed after the clocking event
  // (IEEE 1800-2023 14.16.2)
  initial begin
    @(dcb);
    dcb.req <= 1;
    dcb.req <= ##1 0;
    pulse(1);
    dcb.zreq <= ##0 1;
    dcb.zreq <= 2;
    @(dcb);
    dcb.req <= 2;
    dcb.req <= ##1 0;
    pulse(0);
    pulse(2);
    // Pending drives are not subprocesses (IEEE 1800-2023 9.6.3)
    disable fork;
  end
endprogram

program chk;
  Monitor mon;
  Driver cdrv;
  bit [7:0] bus_seen;
  bit [7:0] nba_value;
  bit [7:0] dly_value;

  task automatic send();
    t.task_data <= 8'ha5;
    t.vck.task_valid <= 1;
  endtask

  // Waiters are declared before the drivers, so they are resumed first if they are
  // woken before the NBA updates of the same Re-NBA region are applied
  initial begin
    @(posedge t.valid);
    `checkh(t.data, 8'h5a)
  end
  initial begin
    @(posedge t.task_valid);
    `checkh(t.task_data, 8'ha5)
  end
  initial begin
    @(posedge t.bus.valid);
    bus_seen = t.bus.data;
  end

  initial begin
    @(t.vck);
    t.data <= 8'h5a;
    t.vck.valid <= 1;
    send();
    // Pending NBA updates are not subprocesses (IEEE 1800-2023 9.6.1)
    wait fork;
    `checkh(t.data, 8'h00)
  end

  initial begin
    nba_value <= 8'h11;
    dly_value <= #2 8'h22;
    disable fork;
    #3;
    `checkh(nba_value, 8'h11)
    `checkh(dly_value, 8'h22)
  end

  // NBAs from class methods run by the program
  initial begin
    mon = new;
    cdrv = new;
    mon.vif = t.bus;
    cdrv.vif = t.bus;
    fork
      mon.run();
      cdrv.run();
    join_none
  end

  initial begin
    @(posedge t.clk);
    ->t.x;
  end

  initial begin
    #40;
    `checks(t.req_log, "1@5 2@15 0@25 ")
    `checks(t.task_req_log, "1@5 2@15 0@25 ")
    `checks(t.zreq_log, "2@5 ")
    `checks(t.mzreq_log, "2@5 ")
    `checks(t.a_log, "0@5 1@5 ")
    `checks(t.bus_req_log, "1@5 2@15 0@25 ")
    `checkh(t.valid, 1'b1)
    `checkh(t.task_valid, 1'b1)
    `checkh(bus_seen, 8'hc3)
    `checkh(mon.seen, 8'hc3)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endprogram
