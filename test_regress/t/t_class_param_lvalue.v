// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
endclass

class Bar #(type BASE=Foo) extends BASE;
  task body();
    int v = 0;
    v = 1;
  endtask
endclass
