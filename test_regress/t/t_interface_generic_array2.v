// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

module GenericModule (interface a[4]);
  initial begin
    #1;
    if (a[0].v != 'hdead) $stop;
    if (a[1].v != 'hbeef) $stop;
    if (a[2].v != 'hface) $stop;
    if (a[3].v != 'hcafe) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module t;
  inf inf_inst[4]();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst[0].v ='hdead;
    inf_inst[1].v ='hbeef;
    inf_inst[2].v ='hface;
    inf_inst[3].v ='hcafe;
  end
endmodule
