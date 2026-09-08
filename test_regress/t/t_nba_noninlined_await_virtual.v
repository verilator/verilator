// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Base;
  virtual task automatic wait_posedge(bit b = 0);
  endtask
  virtual task automatic wait_posedge2(bit b = 0);
  endtask
endclass

module t;
  bit a;
  bit clk;
  assign #10 clk = ~clk;

  class Bar extends Base;
    task automatic wait_posedge(bit b = 0);
      if (!b) begin
        wait_posedge2(~b);
        return;
      end
      @(posedge clk);
    endtask
    task automatic wait_posedge2(bit b = 0);
      if (!b) begin
        wait_posedge(~b);
        return;
      end
      @(posedge clk);
    endtask
  endclass

  Base base;

  task static foo();
    base.wait_posedge();
    a <= 1'b1;
    base.wait_posedge2();
    `checkh(a, 1);
  endtask

  initial begin
    static Bar bar = new;
    base = bar;
    foo();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
