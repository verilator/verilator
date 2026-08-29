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

  bit [2:0] y5;
  bit [2:0] z5;
  assign z5[0] = 1'b1;
  assign z5[1] = !(y5[0]);
  assign z5[2] = !(|y5[1:0]);

  static bit [2:0] expected[5] = {3'b111, 3'b111, 3'b111, 3'b111, 3'b111};

  `define check \
    do begin #1; \
      `checkh(z, expected[0]); \
      `checkh(z2, expected[1]); \
      `checkh(z3, expected[2]); \
      `checkh(z4, expected[3]); \
      `checkh(z5, expected[4]); \
    end while(0)

  class A;
    virtual function int bar();
      // verilator no_inline_task
      y2 = 3'b111;
      expected[1] = 3'b001;
      return 1;
    endfunction
    virtual task foo();
      y3 = 3'b111;
      expected[2] = 3'b001;
    endtask
    virtual task a(bit x = 0);
      x = ~x;  // unused variable usage
      #1;
    endtask
  endclass

  class B extends A;
    task b(bit x = 0);
      // verilator no_inline_task
      if (!x) a(!x);
    endtask
  endclass

  // Commented out code defining/using BarIface is disabled due to issue: #6908
  // interface class BarIface;
  //   pure virtual function int bar();
  // endclass

  class C extends B /* implements BarIface */;
    task foo();
      y = 3'b111;
      expected[0] = 3'b001;
    endtask
    task a(bit x = 0);
      // verilator no_inline_task
      y4 = ~y4;
      expected[3] = {~expected[3][2:1], 1'b1};
      #1;
      if (!x) b(!x);
    endtask
    task b(bit x = 0);
      x = ~x;  // unused variable usage
      #1;
    endtask
  endclass

  class Base;
    virtual task foo();
      y5 = 3'b111;
      expected[4] = 3'b001;
    endtask
  endclass

  class Derived extends Base;
  endclass

  initial begin
    static A aa = new;
    static B bb = new;
    static A ab = bb;
    static C cc = new;
    static A ac = cc;
    static B bc = cc;
    static Derived derived = new;
    // static BarIface bar = cc;
    `check;
    aa.a();
    `check;
    ab.a();
    `check;
    bb.b();
    `check;
    cc.b();
    `check;
    bc.b();
    `check;
    bc.a();
    `check;
    bc.foo();
    `check;
    bb.foo();
    `check;
    // void'(bar.bar());
    `check;
    derived.foo();
    `check;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
