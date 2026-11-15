// DESCRIPTION: Verilator: Clocked processes reading members through virtual interfaces read
// them before their NBA updates, also with threads
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
  int y;
  int z;
  int cnt;
  always @(posedge clk) cnt <= cnt + 1;
endinterface

interface sbus (
    input bit clk
);
  bus s (.clk);
endinterface

class Holder;
  virtual bus vif;
endclass

// Some work, so the processes run in several threads
function automatic int work(int seed);
  int a = seed;
  for (int i = 0; i < 300; ++i) a = a * 1103515245 + 12345 + i;
  return a;
endfunction

module reader (
    input bit clk,
    input int k
);
  virtual bus r;
  Holder h = new;
  bit rst_n = 1;
  int seen_x;
  int seen_y;
  int seen_z;
  int seen_cnt;
  int seen_rst;
  int acc;
  always @(posedge clk) begin
    acc <= work(acc + k);
    seen_x <= r.x;
    seen_y <= h.vif.y;
    seen_z <= r.z;
    seen_cnt <= r.cnt;
  end
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) seen_rst <= 0;
    else seen_rst <= r.x;
  end
endmodule

// Reads, through a virtual interface, the instance connected to the port
module binder (
    input bit clk,
    bus p
);
  virtual bus v;
  int seen_cnt;
  initial v = p;
  always @(posedge clk) seen_cnt <= v.cnt;
endmodule

module t;
  bit clk;
  bus a (.clk);
  virtual bus w = a;
  int cyc;
  int acc;
  reader r0 (
      .clk,
      .k(0)
  );
  reader r1 (
      .clk,
      .k(1)
  );
  always #5 clk = ~clk;
  always @(posedge clk) begin
    acc <= work(acc);
    a.x <= cyc;
    a.y <= cyc;
    cyc <= cyc + 1;
  end
  // Through a virtual interface, from a process that can suspend
  initial
    forever begin
      @(posedge clk);
      w.z <= cyc;
    end
  initial begin
    r0.r = a;
    r1.r = a;
    r0.h.vif = a;
    r1.h.vif = a;
  end
  // Through a virtual interface bound to an interface port
  bus pd (.clk);
  binder bind_d (
      .clk,
      .p(pd)
  );
  // Through an element of an array of virtual interfaces
  bus pa[2] (.clk);
  virtual bus vpa[2];
  int k = 1;
  int seen_a;
  initial vpa = pa;
  always @(posedge clk) seen_a <= vpa[k].cnt;
  // Through a sub-interface of a virtual interface
  sbus g (.clk);
  virtual sbus vg = g;
  int seen_g;
  always @(posedge clk) seen_g <= vg.s.cnt;
  always @(negedge clk) begin
    if (cyc >= 2) begin
      `checkd(r0.seen_x, cyc - 2);
      `checkd(r1.seen_x, cyc - 2);
      `checkd(r0.seen_y, cyc - 2);
      `checkd(r1.seen_y, cyc - 2);
      `checkd(r0.seen_z, cyc - 2);
      `checkd(r0.seen_cnt, cyc - 1);
      `checkd(r0.seen_rst, cyc - 2);
      `checkd(bind_d.seen_cnt, cyc - 1);
      `checkd(seen_a, cyc - 1);
      `checkd(seen_g, cyc - 1);
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
