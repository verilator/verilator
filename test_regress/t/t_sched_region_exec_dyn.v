// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  int mid = 0;
  int flag = 0;
  int seen = 0;
  task waiter();
    wait (flag == 3);
    seen = 7;
  endtask
endclass

module t;
  Cls c = new;
  logic clk = 0;
  logic other = 0;
  logic later = 0;
  int count = 0;

  // Wait conditions are evaluated in the Active region and change state as a
  // side effect, two Active passes after the clock edge
  function automatic bit relay(int x, bit y);
    if (x == 5) c.flag = 3;
    return (x == 5) & y;
  endfunction
  function automatic bit source(bit x, bit y);
    if (x) c.mid = 5;
    return x & y;
  endfunction

  clocking cb @(posedge clk);
    input #0 sampled = c.seen;
  endclocking

  initial c.waiter();
  initial begin
    #1;
    wait (relay(c.mid, later));
  end
  initial begin
    #2;
    wait (source(clk, later));
  end
  always @(posedge other) count <= count + 11;

  initial begin
    #3 clk = 1;
    #1;
    `checkd(cb.sampled, 7);
    `checkd(c.seen, 7);
    #96 other = 1;
    later = 1;
    #1;
    `checkd(count, 11);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
