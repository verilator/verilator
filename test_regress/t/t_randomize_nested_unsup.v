// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class A;
  rand logic [31:0] rdata;
endclass

module t;
  A a;
  A aa;
  initial begin
    a = new;
    aa = new;
    if (a.randomize() with {rdata == aa.randomize();} == 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
