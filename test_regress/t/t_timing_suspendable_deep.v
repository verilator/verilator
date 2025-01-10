// DESCRIPTION: Verilator: Verilog Test module for specialized type default values
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ns

event evt;

class Baz;
  virtual task do_something(); endtask
endclass

class Foo extends Baz;
endclass

class Bar extends Foo;
  virtual task do_something();
    @evt $display("Hello");
  endtask
endclass

module top();
  initial begin
    Bar bar;
    bar = new;

    fork
      #10 bar.do_something();
      #20 $display("world!");
      #10 ->evt;
    join
  end
endmodule
