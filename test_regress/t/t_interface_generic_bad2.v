// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class inf;
  int v;
endclass

module GenericModule (interface a);
  initial begin
    #1;
    if (a.v != 7) $stop;
    if (b.k != 9) $stop;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.v = 7;
    inf_inst2.k = 9;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
