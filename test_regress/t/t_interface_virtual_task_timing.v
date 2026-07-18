// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

package t_pkg;
  bit go = 0;
endpackage

interface clkif (
    input logic clk
);
  int id = 0;
  clocking cb @(posedge clk);
  endclocking
  task automatic wait_clks_cb(int n, output int seen_id);
    repeat (n) @cb;
    seen_id = id;
  endtask
  task automatic wait_clks_raw(int n, output int seen_id);
    repeat (n) @(posedge clk);
    seen_id = id;
  endtask
  task automatic wait_clks_lvl(int n, output int seen_id);
    repeat (n) begin
      wait (clk == 1'b0);
      wait (clk == 1'b1);
    end
    seen_id = id;
  endtask
  task automatic wait_intra(output int seen_id);
    seen_id = @cb id;
  endtask
  task automatic wait_until_id(int target, output int seen_id);
    wait (id == target);
    seen_id = id;
  endtask
  task automatic wait_pkg_go(output int seen_id);
    wait (t_pkg::go);
    seen_id = id;
  endtask
endinterface

interface wrapif (
    input logic clk
);
  clkif nested_if (.clk(clk));
endinterface

class Waiter;
  virtual clkif m_vif;
  function new(virtual clkif vif);
    m_vif = vif;
  endfunction
  task wait_clks(int n, output int seen_id);
    m_vif.wait_clks_cb(n, seen_id);
  endtask
endclass

module t;
  logic slow_clk = 0, fast_clk = 0;
  always #50 slow_clk = ~slow_clk;  // 100 time-unit period
  always #7 fast_clk = ~fast_clk;  // 14 time-unit period

  clkif main_s (.clk(slow_clk));  // id=1, the vif target
  clkif sib_f (.clk(fast_clk));  // id=2, sibling decoy
  wrapif wrap_f (.clk(fast_clk));  // id=3, nested decoy

  int mod_cnt = 0;
  task automatic wait_mod_cnt(int target);
    wait (mod_cnt == target);
  endtask

  task automatic check(string name, realtime dt, realtime lo, realtime hi, int seen_id, int exp_id);
    if (dt < lo || dt > hi || seen_id != exp_id) begin
      $display("%%Error: %s: dt=%0t seen_id=%0d expected id=%0d dt=[%0t:%0t]", name, dt, seen_id,
               exp_id, lo, hi);
      $stop;
    end
  endtask

  initial begin
    virtual clkif vs, vf;
    int seen_id;
    realtime t0;
    Waiter w;
    vs = main_s;
    vf = sib_f;
    main_s.id = 1;
    sib_f.id = 2;
    wrap_f.nested_if.id = 3;
    w = new(main_s);
    #1000;

    // Task body waits on the clocking block event of the slow instance
    t0 = $realtime;
    seen_id = -1;
    vs.wait_clks_cb(2, seen_id);
    check("cb_task", $realtime - t0, 100, 200, seen_id, 1);

    // Task body waits on a raw posedge of the slow instance's clock
    t0 = $realtime;
    seen_id = -1;
    vs.wait_clks_raw(2, seen_id);
    check("raw_task", $realtime - t0, 100, 200, seen_id, 1);

    // Task body uses level waits on the slow instance's clock
    t0 = $realtime;
    seen_id = -1;
    vs.wait_clks_lvl(2, seen_id);
    check("lvl_task", $realtime - t0, 100, 200, seen_id, 1);

    // Intra-assignment event control; aligned so the next cb event is 50 away
    @(negedge slow_clk);
    t0 = $realtime;
    seen_id = -1;
    vs.wait_intra(seen_id);
    check("intra_task", $realtime - t0, 40, 60, seen_id, 1);

    // Call-site event control through the handle
    t0 = $realtime;
    seen_id = -1;
    repeat (2) @vs.cb;
    seen_id = vs.id;
    check("call_site", $realtime - t0, 100, 200, seen_id, 1);

    // Class method wrapping the virtual interface call (UVM shape)
    t0 = $realtime;
    seen_id = -1;
    w.wait_clks(2, seen_id);
    check("class_vif", $realtime - t0, 100, 200, seen_id, 1);

    // Second handle to the fast instance: per-call dispatch both ways
    t0 = $realtime;
    seen_id = -1;
    vf.wait_clks_cb(2, seen_id);
    check("vif_fast", $realtime - t0, 1, 56, seen_id, 2);

    t0 = $realtime;
    seen_id = -1;
    vs.wait_clks_cb(2, seen_id);
    check("vif_slow_again", $realtime - t0, 100, 200, seen_id, 1);

    // Hierarchical (non-virtual) call must keep timing on its own instance
    t0 = $realtime;
    seen_id = -1;
    sib_f.wait_clks_cb(2, seen_id);
    check("hier_fast", $realtime - t0, 1, 56, seen_id, 2);

    // Wait condition mixing the member with a task argument
    fork
      #30 main_s.id = 42;
    join_none
    t0 = $realtime;
    seen_id = -1;
    vs.wait_until_id(42, seen_id);
    check("wait_arg", $realtime - t0, 25, 35, seen_id, 42);
    main_s.id = 1;

    // Wait condition on a package variable inside the interface task
    fork
      #20 t_pkg::go = 1'b1;
    join_none
    t0 = $realtime;
    seen_id = -1;
    vs.wait_pkg_go(seen_id);
    check("wait_pkg", $realtime - t0, 15, 25, seen_id, 1);

    // Module-task wait on a task argument stays on the module path
    fork
      #10 mod_cnt = 5;
    join_none
    t0 = $realtime;
    wait_mod_cnt(5);
    check("wait_mod", $realtime - t0, 5, 15, mod_cnt, 5);

    // Wait on an automatic local in a procedure context
    begin
      automatic int tgt = 42;
      fork
        #10 mod_cnt = 42;
      join_none
      t0 = $realtime;
      wait (mod_cnt == tgt);
      check("wait_auto", $realtime - t0, 5, 15, mod_cnt, 42);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #100000;
    $display("%%Error: timeout");
    $stop;
  end
endmodule
