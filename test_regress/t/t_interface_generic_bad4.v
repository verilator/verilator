// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

module GenericModule (interface a);
  initial begin
    #1;
    if (a.v != 7) $stop;
    if (b.k != 9) $stop;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst, inf_inst);
  initial begin
    inf_inst.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
