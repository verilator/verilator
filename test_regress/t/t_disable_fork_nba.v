// DESCRIPTION: Verilator: Pending NBA updates are not subprocesses for disable/wait fork
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface bus_if;
  int data;
endinterface

class Cls;
  virtual bus_if vif;
  task set(int v);
    vif.data <= v;
  endtask
endclass

module t;
  bit clk;
  int dly_value;
  int wait_value;
  bit [1:0] drive_value;
  bus_if bus ();
  Cls obj = new;

  always #5 clk = ~clk;

  default clocking cb @(posedge clk);
    output drive_value;
  endclocking

  // 'disable fork' does not cancel pending updates (IEEE 1800-2023 9.6.3)
  initial begin
    obj.vif = bus;
    dly_value <= #2 1;
    obj.set(2);
    cb.drive_value <= ##1 3;
    disable fork;
    #20;
    `checkd(dly_value, 1)
    `checkd(bus.data, 2)
    `checkd(drive_value, 3)
  end

  // 'wait fork' does not wait for pending updates (IEEE 1800-2023 9.6.1)
  initial begin
    #30;
    wait_value <= #5 4;
    wait fork;
    `checkd($time, 30)
    #10;
    `checkd(wait_value, 4)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
