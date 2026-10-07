// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// An NBA at time 0 is committed at time 0, also in a process that later calls a task not inlined,
// with a timing control
module sub;
  /*verilator no_inline_module*/
  bit y;
  task automatic pause();
    /*verilator no_inline_task*/
    #2;
  endtask
  initial begin
    y <= 1'b1;
    #1 `checkh(y, 1);
    pause();
  end
endmodule

module t;
  bit a;
  bit clk;
  assign #10 clk = ~clk;

  class Bar;
    task automatic wait_posedge();
      @(posedge clk);
    endtask
  endclass

  Bar bar;
  sub sub_i ();

  task static foo();
    bar.wait_posedge();
    a <= 1'b1;
    bar.wait_posedge();
    `checkh(a, 1);
  endtask

  initial begin
    bar = new;
    foo();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
