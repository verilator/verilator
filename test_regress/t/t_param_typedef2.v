// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo #(type T);
endclass

class Bar #(type T);
endclass

typedef Bar#(string) s;

class Some #(type T);
   typedef Bar#(string) s;
endclass

module t;
   initial begin
      Some#(int)::s x[string];
      Bar#(string) y[string];
      if ($typename(Foo#(s)) != $typename(Foo#(Bar#(string)))) $stop;
      if ($typename(x) != $typename(y)) $stop;
      $write("*-* All finished *-*\n");
      $finish;
   end
endmodule
