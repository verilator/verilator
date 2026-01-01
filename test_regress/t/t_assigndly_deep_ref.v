// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface Iface;
  bit clk;
  int x;

  clocking cb @(posedge clk);
    default input #0 output #0;
    inout x;
  endclocking
endinterface

class Foo;
  virtual Iface iface;
  function new(virtual Iface tmp);
    iface = tmp;
  endfunction
  task update(virtual Iface tmp);
    iface = tmp;
  endtask
endclass

class Bar;
  Foo foo;
  function new(Foo tmp);
    foo = tmp;
  endfunction
  task update(Foo tmp);
    foo = tmp;
  endtask
  task assignment();
    foo.iface.cb.x <= 8;
  endtask
endclass

module t;
  Iface iface ();
  Iface iface2 ();

  task clockSome();
    #2;
    iface.clk = ~iface.clk;
    iface2.clk = ~iface2.clk;
    #2;
    iface.clk = ~iface.clk;
    iface2.clk = ~iface2.clk;
  endtask

  initial begin
    Foo foo = new(iface);
    Foo foo2 = new(iface2);
    Bar bar = new(foo);
    clockSome();
    if (iface.x != 0) $stop;
    if (iface2.x != 0) $stop;
    bar.assignment();
    clockSome();
    if (iface.x != 8) $stop;
    if (iface2.x != 0) $stop;
    foo.update(iface2);
    clockSome();
    if (iface.x != 8) $stop;
    if (iface2.x != 0) $stop;
    bar.update(foo2);
    clockSome();
    if (iface.x != 8) $stop;
    if (iface2.x != 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
