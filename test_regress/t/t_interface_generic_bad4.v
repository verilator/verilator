// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

interface inf2;
  int k;
endinterface

module GenericModule (interface a, interface b);
  initial begin
    #1;
    if (a.v != 7) $stop;
    if (b.k != 9) $stop;
  end
endmodule

module t;
  int inf_inst;
  inf2 inf_inst2();
  GenericModule genericModule (inf_inst, inf_inst2);
  initial begin
    inf_inst.v = 7;
    inf_inst2.k = 9;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
