// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

module GenericModule (interface a, inf b, interface c);
  initial begin
    #1;
    if (a.v != 7) $stop;
    if (b.v != 8) $stop;
    if (c.v != 9) $stop;
  end
endmodule

module t;
  inf inf_inst[3]();
  GenericModule genericModule (inf_inst[0], inf_inst[1], inf_inst[2]);
  initial begin
    inf_inst[0].v = 7;
    inf_inst[1].v = 8;
    inf_inst[2].v = 9;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
