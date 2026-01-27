// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Foo;
endclass

class Bar #(type BASE=Foo) extends BASE;
  task body();
    int v = 0;
    v = 1;
  endtask
endclass
