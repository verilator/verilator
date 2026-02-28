// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo #(type T);
endclass

class Bar #(type T);
endclass

typedef Bar#(string) s_t;

class Some #(type T);
  typedef Bar#(string) s_t;
endclass

module t;
  initial begin
    Some#(int)::s_t x[string];
    Bar#(string) y[string];
    if ($typename(Foo#(s_t)) != $typename(Foo#(Bar#(string)))) $stop;
    if ($typename(x) != $typename(y)) $stop;
    $write("*-* All finished *-*\n");
    $finish;
  end
endmodule
