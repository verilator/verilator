// DESCRIPTION: Verilator: Clocked processes reading members through virtual interfaces, also
// held by classes, read them before their NBA updates, also with threads
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
  always @(negedge clk) begin
    if (cyc >= 2) begin
      `checkd(r0.seen_x, cyc - 2);
      `checkd(r1.seen_x, cyc - 2);
      `checkd(r0.seen_y, cyc - 2);
      `checkd(r1.seen_y, cyc - 2);
      `checkd(r0.seen_z, cyc - 2);
      `checkd(r0.seen_cnt, cyc - 1);
      `checkd(r0.seen_rst, cyc - 2);
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
