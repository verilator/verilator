// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Cycle delay in a class nested in an interface uses the interface default clocking

interface intf (
    input bit clk
);
  int ticks = 0;
  logic a = 1;
  logic b = 1;
  always @(posedge clk) ++ticks;

  default clocking ck @(posedge clk);
  endclocking

  class Waiter;
    task wait_cycles(int n);
      ##(n);
    endtask
    task wait_one();
      ##1;
    endtask
    task check_prop();
      assert property (a |-> ##1 b);
    endtask
  endclass

  Waiter waiter = new;
endinterface

module t;
  bit clk;
  always #5 clk = ~clk;

  intf i (clk);

  initial begin
    int start;
    @(posedge clk);
    start = i.ticks;
    i.waiter.wait_cycles(5);
    `checkd(i.ticks - start, 5);
    start = i.ticks;
    i.waiter.wait_one();
    `checkd(i.ticks - start, 1);
    i.waiter.check_prop();
    i.waiter.wait_cycles(3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
