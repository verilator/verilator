// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  localparam lparam = 12;

  int v;
  modport mp (
    input v
  );
endinterface

module GenericModule (interface.mp a);
  initial begin
    if (a.lparam != 12) $stop;
    if (a.v != 7) $stop;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
