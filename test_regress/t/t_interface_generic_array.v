// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

module GenericModule (interface a);
  initial begin
    #1;
    if (a.v != 7) $stop;
    a.v = 9;
  end
endmodule

module t;
  inf inf_inst[3]();
  GenericModule genericModule (inf_inst[2]);
  initial begin
    inf_inst[2].v = 7;
    #2;
    if (inf_inst[2].v != 9) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
