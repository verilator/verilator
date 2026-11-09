// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package pkg;
  bit [2:0] y3;
endpackage

module t;
  bit [2:0] y;
  bit [2:0] z;
  assign z[0] = 1'b1;
  assign z[1] = !(y[0]);
  assign z[2] = !(|y[1:0]);

  bit [2:0] y2;
  bit [2:0] z2;
  assign z2[0] = 1'b1;
  assign z2[1] = !(y2[0]);
  assign z2[2] = !(|y2[1:0]);

  import pkg::y3;
  bit [2:0] z3;
  assign z3[0] = 1'b1;
  assign z3[1] = !(y3[0]);
  assign z3[2] = !(|y3[1:0]);

  bit [2:0] y4;
  bit [2:0] z4;
  assign z4[0] = 1'b1;
  assign z4[1] = !(y4[0]);
  assign z4[2] = !(|y4[1:0]);
  class Foo;
    function automatic int bar();
      // verilator no_inline_task
      y2 = 3'b111;
      y3 = 3'b111;
      return 1;
    endfunction
    task run();
      y = 3'b111;
      #1;
      `checkh(z, 3'b001);
      `checkh(z2, 3'b001);
      `checkh(z3, 3'b001);
      `checkh(z4, 3'b111);
    endtask
    task a(bit x = 0);
      // verilator no_inline_task
      y4 = ~y4;
      #1;
      if (!x) b(!x);
    endtask
    task b(bit x = 0);
      // verilator no_inline_task
      if (!x) a(!x);
    endtask
  endclass

  // 'y5' is written by a suspendable process, so 'z5' must be re-evaluated whenever that
  // process can resume, including on events waited on in the tasks it calls
  event ev;
  bit [2:0] y5;
  bit [2:0] z5;
  assign z5[0] = 1'b1;
  assign z5[1] = !(y5[0]);
  assign z5[2] = !(|y5[1:0]);
  class Cls;
    // 'f' calls 'b' and 'c', 'b' calls 'f', and 'c' calls 'b'. Calling any of these tasks can
    // wait on 'ev' in 'f', including 'c', which only reaches 'f' via 'b'.
    task f(int n);
      // verilator no_inline_task
      if (n > 0) begin
        b(n - 1);
        c(n - 1);
      end
      @(ev);
    endtask
    task b(int n);
      // verilator no_inline_task
      if (n > 0) f(n - 1);
    endtask
    task c(int n);
      // verilator no_inline_task
      b(n);
    endtask
  endclass
  Cls obj = new;
  // Calls 'f' directly. Keep this before the process below in the source: the bug only showed
  // when 'f' was analysed before 'c'.
  initial obj.f(1);
  // Only calls 'c', so can resume on 'ev' only via 'c -> b -> f', then writes 'y5'
  initial begin
    obj.c(1);
    y5 = 3'b111;
  end
  // Trigger 'ev', then check 'z5' was updated after the write to 'y5' on resumption
  initial begin
    #2;
    `checkh(z5, 3'b111);
    ->ev;
    #1;
    `checkh(z5, 3'b001);
  end

  initial begin
    static Foo foo = new;
    #1;
    `checkh(z, 3'b111);
    `checkh(z2, 3'b111);
    `checkh(z3, 3'b111);
    `checkh(z4, 3'b111);
    void'(foo.bar());
    #1;
    `checkh(z, 3'b111);
    `checkh(z2, 3'b001);
    `checkh(z3, 3'b001);
    `checkh(z4, 3'b111);
    foo.run();
    foo.a();
    `checkh(z, 3'b001);
    `checkh(z2, 3'b001);
    `checkh(z3, 3'b001);
    `checkh(z4, 3'b001);
    foo.b();
    `checkh(z, 3'b001);
    `checkh(z2, 3'b001);
    `checkh(z3, 3'b001);
    `checkh(z4, 3'b111);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
