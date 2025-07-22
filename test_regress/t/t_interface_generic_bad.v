// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf2;
  int v;
endinterface

module GenericModule (interface a, interface b);
  initial begin
    #1;
    if (b.v != 7) $stop;
  end
endmodule

module t;
  inf inf_inst();
  inf2 inf_inst2();
  GenericModule genericModule (inf_inst, inf_inst2);
  initial begin
    inf_inst2.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
