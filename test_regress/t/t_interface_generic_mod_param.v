// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

module GenericModule#(type T, type Y = int) (interface a);
  initial begin
    if (a.v != 7) $stop;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule #(string) genericModule (inf_inst);
  initial begin
    inf_inst.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
