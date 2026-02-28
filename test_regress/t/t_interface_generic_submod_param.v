// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module sub #(parameter P);
endmodule

package pkg;
  parameter A = 3;
endpackage

class B;
  int x;
endclass

module Gm (interface a);
  B b;
  sub#(.P(pkg::A + $bits(b.x))) s();
  initial begin
    a.v = s.P;
  end
endmodule

interface inf;
  int v;
endinterface

module t;
  inf i();
  Gm g(.a(i));
  initial begin
    #1;
    if (i.v != 35) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
