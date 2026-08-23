// DESCRIPTION: Verilator: Program event region scheduling test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class region_waiter;
  event wake;
  string order;

  task run(bit reactive_thread);
    @wake;
    order = {order, reactive_thread ? "p" : "m"};
    #0;
    order = {order, reactive_thread ? "P" : "M"};
  endtask

  task write_nba(bit [6:0] value);
    t.nba_value <= value;
  endtask
endclass

interface region_interface;
  event wake;
  int stage;
  int wake_time;

  task automatic run;
    #1;
    stage = 1;
    @wake;
    wake_time = int'($time);
    #0 stage = 2;
    #0 stage = 3;
  endtask
endinterface

module t;
  event wake;
  string order;
  bit design_ready;
  bit initial_seen;
  bit [6:0] initial_value;
  wire [6:0] initial_comb = initial_value ^ 7'h55;
  event task_wake;
  string task_order;
  event shared_wake;
  string shared_order;
  int active_wakes;
  int reactive_wakes;
  int reactive_stage;
  region_waiter dyn = new;
  bit [6:0] nba_value;
  wire [6:0] nba_comb = nba_value + 7'd3;
  int nba_stage;
  event fork_wake;
  bit fork_child;
  bit fork_parent;
  bit fork_module;
  bit [6:0] region_value;
  wire [6:0] region_comb = {region_value[0], region_value[6:1]} ^ 7'h55;
  wire region_clk = region_value == 7'd39;
  bit [6:0] last_comb;
  int comb_changes;
  int clock_rises;
  int clock_falls;

  region_module m ();
  region_program p ();
  region_interface ifc ();

  function void record(string value);
    order = {order, value};
  endfunction

  task automatic shared_delay(bit reactive_thread);
    #1;
    if (reactive_thread) begin
      task_order = {task_order, "d"};
      ->task_wake;
      #(int'($time) - 10) task_order = {task_order, "e"};
      #0 task_order = {task_order, "f"};
    end
    else begin
      task_order = {task_order, "a"};
      @task_wake;
      task_order = {task_order, "b"};
      #0 task_order = {task_order, "c"};
    end
  endtask

  task automatic shared_event(bit reactive_thread);
    for (int i = 0; i < 2; ++i) begin
      @shared_wake;
      if (reactive_thread) begin
        `checkd(active_wakes, 1)
        ++reactive_wakes;
        if (i == 1) begin
          `checkd(reactive_stage, 1)
          reactive_stage = 2;
        end
      end
      else begin
        `checkd(reactive_wakes, i == 0 ? 0 : 2)
        if (i == 1) `checkd(reactive_stage, 4)
        ++active_wakes;
      end
      if (i == 0) shared_order = {shared_order, reactive_thread ? "p" : "m"};
      #0;
      if (i == 0) shared_order = {shared_order, reactive_thread ? "P" : "M"};
    end
  endtask

  initial #0 design_ready = 1;
  initial #9 shared_delay(0);
  initial #11 shared_event(0);
  initial #12 ->shared_wake;
  initial #16 dyn.run(0);
  initial #17 ->dyn.wake;
  always @(region_comb) begin
    if ($time != 0) begin
      ++comb_changes;
      last_comb = region_comb;
    end
  end
  always @(posedge region_clk) if ($time != 0) ++clock_rises;
  always @(negedge region_clk) if ($time != 0) ++clock_falls;
  initial begin
    @(nba_value);
    `checkd(nba_stage, 2)
  end
  initial begin
    #24;
    dyn.write_nba(7'd27);
    #0;
    `checkd(nba_value, 23)
  end
  initial begin
    @fork_wake;
    `checkd(fork_child, 1)
    `checkd(fork_parent, 1)
    fork_module = 1;
  end
  initial begin
    #28 ->ifc.wake;
    #1 ->ifc.wake;
  end

  initial begin
    #6;
    `checks(order, "adefbc")
    $display("%s", order);
    `checkd(initial_seen, 1)
    `checkd(initial_comb, 7'h76)
    `checkd(comb_changes, 4)
    `checkd(last_comb, 7'h4f)
    `checkd(clock_rises, 1)
    `checkd(clock_falls, 1)
    #26;
    `checks(task_order, "adefbc")
    `checks(shared_order, "mMpP")
    `checkd(active_wakes, 2)
    `checkd(reactive_wakes, 2)
    `checks(dyn.order, "mMpP")
    `checkd(nba_value, 27)
    `checkd(nba_comb, 7'd30)
    `checkd(nba_stage, 2)
    `checkd(fork_module, 1)
    `checkd(ifc.stage, 3)
    `checkd(ifc.wake_time, 29)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module region_module;
  initial begin
    #5 t.record("a");
    @t.wake;
    t.record("b");
    #0 t.record("c");
  end
endmodule

program region_program;
  initial #100;

  initial begin
    #1;
    repeat (4) begin
      #1 t.region_value += 7'd13;
      #0;
    end
  end

  initial begin
    `checkd(t.design_ready, 1)
    t.initial_seen = 1;
    t.initial_value = 7'h23;
  end

  initial begin
    #5 t.record("d");
    ->t.wake;
    #0 t.record("e");
    #0 t.record("f");
  end

  initial #9 t.shared_delay(1);
  initial #11 t.shared_event(1);
  initial #16 t.dyn.run(1);

  initial begin
    #14;
    t.reactive_stage = 1;
    ->t.shared_wake;
    #0;
    `checkd(t.reactive_stage, 2)
    t.reactive_stage = 3;
    #0 t.reactive_stage = 4;
  end

  initial begin
    #20;
    t.nba_value <= 7'd15;
    #0;
    `checkd(t.nba_value, 0)
    #0;
    `checkd(t.nba_value, 0)
    @(t.nba_value);
    `checkd(t.nba_value, 15)
    t.nba_stage = 1;
    #0 t.nba_stage = 2;
    #2;
    t.dyn.write_nba(7'd23);
    #0;
    `checkd(t.nba_value, 15)
    #2;
    `checkd(t.nba_value, 27)
  end

  initial begin
    #26;
    ->t.fork_wake;
    fork
      #0 t.fork_child = 1;
    join_none
    wait fork;
    `checkd(t.fork_module, 0)
    `checkd(t.fork_child, 1)
    #0 t.fork_parent = 1;
  end

  initial #27 t.ifc.run();
endprogram
