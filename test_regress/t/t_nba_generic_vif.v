// DESCRIPTION: Verilator: NBAs through virtual interfaces update the members after clocked
// processes read them directly, also with threads, also NBAs in methods of the interface
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus (
    input bit clk
);
  int x;
  int z;
  int m;
  event ev;
  function void set_m(int v);
    m <= v;
  endfunction
  task automatic set_m_at_clk(int v);
    @(posedge clk);
    m <= v;
  endtask
  function void fire();
    ->>ev;
  endfunction
endinterface

class Driver;
  virtual bus vif;
  function new(virtual bus v);
    vif = v;
  endfunction
  function void set_m(int v);
    vif.set_m(v);
  endfunction
  task set_m_at_clk(int v);
    vif.set_m_at_clk(v);
  endtask
  function void fire();
    vif.fire();
  endfunction
endclass

// Some work, so the processes run in several threads
function automatic int work(int seed);
  int a = seed;
  for (int i = 0; i < 300; ++i) a = a * 1103515245 + 12345 + i;
  return a;
endfunction

module t;
  bit clk;
  int cyc;
  always #5 clk = ~clk;

  bus a0 (clk);
  bus a1 (clk);
  virtual bus w0 = a0;
  virtual bus w1 = a1;

  int acc;
  always @(posedge clk) begin
    acc <= work(acc);
    cyc <= cyc + 1;
    w0.x <= cyc;
    w1.x <= cyc + 100;
  end
  // From a process that can suspend
  initial
    forever begin
      @(posedge clk);
      w1.z <= cyc;
    end

  // Clocked processes reading the members directly, before the NBA updates
  int acc0;
  int seen0_x;
  always @(posedge clk) begin
    acc0 <= work(acc0 + 1);
    seen0_x <= a0.x;
  end
  int acc1;
  int seen1_x;
  int seen1_z;
  always @(posedge clk) begin
    acc1 <= work(acc1 + 2);
    seen1_x <= a1.x;
    seen1_z <= a1.z;
  end
  // Combinational logic reading a member directly, after the NBA updates
  int comb_x;
  assign comb_x = a1.x;

  // NBAs in methods of the interface called through the handles update the instance the handle
  // selects
  int n0_ev;
  int n1_ev;
  always @(a0.ev) ++n0_ev;
  always @(a1.ev) ++n1_ev;
  initial begin
    Driver d0;
    Driver d1;
    d0 = new(w0);
    d1 = new(w1);
    #1;
    d0.set_m(10);
    d1.set_m(11);
    #1;
    `checkd(a0.m, 10);
    `checkd(a1.m, 11);
    fork
      d0.set_m_at_clk(20);
      d1.set_m_at_clk(21);
    join
    #1;
    `checkd(a0.m, 20);
    `checkd(a1.m, 21);
    d0.fire();
    #1;
    `checkd(n0_ev, 1);
    `checkd(n1_ev, 0);
  end

  always @(negedge clk) begin
    if (cyc >= 2) begin
      `checkd(seen0_x, cyc - 2);
      `checkd(seen1_x, cyc - 2 + 100);
      `checkd(seen1_z, cyc - 2);
      `checkd(comb_x, cyc - 1 + 100);
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
