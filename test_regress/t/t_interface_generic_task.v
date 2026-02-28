// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
  task setup();
    v = 3;
  endtask
endinterface

interface inf2;
  int k;
endinterface

module GenericModule (interface a);
  initial begin
    a.setup();
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    #1;
    if (inf_inst.v != 3) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
