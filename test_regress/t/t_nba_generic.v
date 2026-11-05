// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface Ifc (
    input bit clk
);
  bit [7:0] data;
  int cnt;
  always @(posedge clk) data <= data + 1;
  task clear();
    data = 0;
  endtask
endinterface

module t;
  // The loops below are not unrolled, as their bound is not a constant
  int n;
  initial n = 2;

  // The updates are made in the order the NBAs execute (IEEE 1800-2023 4.6)
  initial begin
    int x;
    #1;
    for (int i = 0; i < n; ++i) begin
      if (i == 1) x <= 1;
      if (i == 0) x <= 2;
    end
    #1 `checkh(x, 1);
  end

  // Each execution of an NBA updates the bits its operands selected then (IEEE 1800-2023 10.4.2)
  initial begin
    bit [3:0] v;
    #1;
    for (int i = 0; i < n; ++i) v[i] <= 1'b1;
    #1 `checkh(v, 4'h3);
  end

  // Enqueued updates are committed together with the other NBAs of the same NBA region
  bit clk;
  // verilator lint_off MULTIDRIVEN
  int a;
  // verilator lint_on MULTIDRIVEN
  int b;
  initial a <= 0;  // Makes the NBAs to 'a' enqueued
  always @(posedge clk) begin
    a <= b + 1;
    b <= b + 1;
  end
  initial
    forever begin
      @(a or b);
      `checkh(a, b);
    end
  // Combinational logic reading them is evaluated after the commit
  wire integer a1 = a + 1;
  always @(posedge clk) `checkh(a1, a + 1);
  initial begin
    #1 clk = 1;
    #1 clk = 0;
    #1 clk = 1;
    #1 `checkh(a, 2);
  end

  // An array updated by NBAs in a loop of clocked logic has a queue of its own, which is not
  // reallocated in each evaluation
  int arr[4];
  always @(posedge clk) for (int i = 0; i < n; ++i) arr[i] <= arr[i] + i + 1;
  initial begin
    #4;
    `checkh(arr[0], 2);
    `checkh(arr[1], 4);
    `checkh(arr[2], 0);
  end

  // A blocking assignment in a function called from an initial block is not combinational logic
  Ifc ifc (clk);
  virtual Ifc vif = ifc;
  initial vif.clear();
  initial #4 `checkh(ifc.data, 2);

  // An NBA through a handle updates the member of the instance selected, in the NBA region,
  // in order with the NBAs to the member made directly
  always @(posedge clk) begin
    int old;
    old = vif.cnt;
    ifc.cnt <= 100;
    vif.cnt <= old + 1;
    `checkh(vif.cnt, old);
  end
  initial #4 `checkh(ifc.cnt, 2);

  // Pending updates are not subprocesses, so are neither waited for nor disabled
  // (IEEE 1800-2023 9.6.1, 9.6.3)
  initial begin
    int w;
    #1;
    w <= 1;
    wait fork;
    `checkh(w, 0);
    disable fork;
    #1 `checkh(w, 1);
  end

  // A nonblocking event trigger fires in the NBA region
  event e;
  initial begin
    bit fired;
    fork
      begin
        @(e);
        fired = 1;
      end
    join_none
    #1;
    ->>e;
    #1 `checkh(fired, 1);
  end

  // A process commits its NBAs after resuming on an event it waits on through a cycle of calls
  event ev;
  class Cls;
    // 'f' calls 'b' and 'c', 'b' calls 'f', and 'c' calls 'b', so calling 'c' can wait on 'ev'
    task f(int k);
      // verilator no_inline_task
      if (k > 0) begin
        b(k - 1);
        c(k - 1);
      end
      @(ev);
    endtask
    task b(int k);
      // verilator no_inline_task
      if (k > 0) f(k - 1);
    endtask
    task c(int k);
      // verilator no_inline_task
      b(k);
    endtask
  endclass
  Cls obj = new;
  // Calls 'f' directly. Keep this before the process below in the source: the bug only showed
  // when 'f' was analysed before 'c'.
  initial obj.f(1);
  bit [2:0] y;
  initial begin
    obj.c(1);
    y <= 3'b111;
  end
  initial begin
    #2 `checkh(y, 3'b000);
    ->ev;
    #1 `checkh(y, 3'b111);
  end

  // An update of a value too large to be copied via the stack
  initial begin
    string src[500000];
    string dst[500000];
    foreach (src[i]) src[i] = "x";
    #1;
    dst <= src;
    #1 foreach (dst[i]) `checks(dst[i], "x");
  end

  initial begin
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
