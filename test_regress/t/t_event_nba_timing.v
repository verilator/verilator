// DESCRIPTION: Verilator: Nonblocking event triggers in suspendable processes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  event e;
  event ea[2];
  static event se;
  Cls next;
  task trig_dly();
    #1 ->>e;
    `checkd(e.triggered, 0)
  endtask
endclass

interface ifc;
  event e;
  task trig();
    ->>e;
  endtask
endinterface

module t;
  bit clk;
  event e_init;
  event e_dly;
  event e_clk;
  event e_arr[2];
  int init_time = -1;
  int dly_time = -1;
  int clk_times;
  Cls c1 = new;
  Cls c2 = new;
  Cls c;
  ifc i ();
  virtual ifc vif;
  int idx;
  int x;
  string log;

  always #5 clk = ~clk;

  initial begin
    @e_init;
    init_time = int'($time);
  end
  initial begin
    @e_dly;
    dly_time = int'($time);
  end
  always @e_clk ++clk_times;

  always @(c1.e) log = {log, $sformatf("c1.e@%0d ", $time)};
  always @(Cls::se) log = {log, $sformatf("se@%0d ", $time)};
  always @(c1.ea[0]) log = {log, $sformatf("c1.ea[0]@%0d ", $time)};
  always @(c1.ea[1]) begin
    `checkd(x, 3)
    log = {log, $sformatf("c1.ea[1]@%0d ", $time)};
  end
  always @(c2.ea[0]) log = {log, $sformatf("c2.ea[0]@%0d ", $time)};
  always @(c2.ea[1]) log = {log, $sformatf("c2.ea[1]@%0d ", $time)};
  always @(c2.e) log = {log, $sformatf("c2.e@%0d ", $time)};
  always @(e_arr[0]) log = {log, $sformatf("e_arr[0]@%0d ", $time)};
  always @(e_arr[1]) log = {log, $sformatf("e_arr[1]@%0d ", $time)};
  always @(i.e) log = {log, $sformatf("i.e@%0d ", $time)};

  // The event is triggered in the NBA region (IEEE 1800-2023 15.5.1)
  initial ->>e_init;

  initial begin
    #1 ->>e_dly;
    `checkd(e_dly.triggered, 0)
    #0 `checkd(e_dly.triggered, 0)
  end

  always begin
    @(posedge clk);
    ->>e_clk;
  end

  initial begin
    vif = i;
    // From a suspended class method
    c1.trig_dly();
    // Static class member
    #1 ->>Cls::se;
    // The event triggered is the one referenced when '->>' executes
    #1 c = c1;
    idx = 1;
    ->>c.ea[idx];
    x <= 3;
    c = c2;
    idx = 0;
    #1 idx = 1;
    ->>e_arr[idx];
    idx = 0;
    // From an interface task, called by two processes
    #1 vif.trig();
    // In a loop with a jump
    #2 for (int k = 0; k < 2; ++k) begin
      if (k == 1) break;
      ->>c2.ea[k];
    end
    // Not a subprocess, so not disabled (IEEE 1800-2023 9.6.3)
    #1 fork
      #1 `stop;
    join_none
    ->>c2.e;
    disable fork;
    // Including a handle selected from another
    #1 c1.next = c2;
    ->>c1.next.e;
    c1.next = null;
  end
  initial #6 vif.trig();

  initial begin
    #22;
    `checkd(init_time, 0)
    `checkd(dly_time, 1)
    `checkd(clk_times, 2)
    `checks(log, "c1.e@1 se@2 c1.ea[1]@3 e_arr[1]@4 i.e@5 i.e@6 c2.ea[0]@7 c2.e@8 c2.e@9 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
