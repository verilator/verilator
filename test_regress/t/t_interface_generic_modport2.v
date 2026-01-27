// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
  modport mp (
    output v
  );
endinterface

module GenericModule (interface.mp a);
  initial begin
    a.v = 7;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    #1;
    if (inf_inst.v != 7) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
